//! Evidence for `broker.log-anti-rollback`: an authenticated monotonic head
//! watermark (a `<log>.hw` sidecar) makes the encrypted log tamper-evident against
//! TRUNCATION / ROLLBACK — the one gap per-record sealing leaves. A log rolled back
//! below the watermark, a deleted watermark on a non-empty log, and a tampered
//! watermark are all refused; a normal reopen recovers.
#![cfg(feature = "anti-rollback")]

use astream_broker::BrokerLog;
use astream_wire::Offset;
use std::fs::OpenOptions;
use std::sync::atomic::{AtomicU64, Ordering};

static CTR: AtomicU64 = AtomicU64::new(0);
const KEY: [u8; 32] = [0x3c; 32];

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

/// Remove `path` and every `<path>.*` sidecar in its directory.
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
        }
    }
}

fn tmp(tag: &str) -> (Cleanup, std::path::PathBuf) {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let path = std::env::temp_dir().join(format!("asroll_{tag}_{pid}_{n}.log"));
    (Cleanup::new(&[&path]), path)
}

fn hw_path(log: &std::path::Path) -> std::path::PathBuf {
    let mut s = log.as_os_str().to_os_string();
    s.push(".hw");
    std::path::PathBuf::from(s)
}

fn cleanup(log: &std::path::Path) {
    let _ = std::fs::remove_file(log);
    let _ = std::fs::remove_file(hw_path(log));
}

#[test]
fn a_truncated_log_is_detected_as_rollback() {
    let (_tmp, path) = tmp("rollback");
    cleanup(&path);

    // Establish anti-rollback and commit two records; the watermark is now 2.
    {
        let mut log = BrokerLog::open_encrypted_verified_init(&path, KEY).unwrap();
        log.publish(1, 1, "/a/x".into(), b"one".to_vec()).unwrap();
        log.publish(1, 2, "/a/x".into(), b"two".to_vec()).unwrap();
    }
    let bytes_at_2 = std::fs::metadata(&path).unwrap().len();

    // Reopen (verifies head 2 == watermark 2) and commit two more; watermark -> 4.
    {
        let mut log = BrokerLog::open_encrypted_verified(&path, KEY).unwrap();
        log.publish(1, 3, "/a/x".into(), b"three".to_vec()).unwrap();
        log.publish(1, 4, "/a/x".into(), b"four-must-not-be-erasable".to_vec())
            .unwrap();
        assert_eq!(log.read_from(Offset(0)).len(), 4);
    }

    // Attacker truncates the LOG back to two records (a clean record boundary) but
    // cannot forge a lower authenticated watermark — the sidecar still says 4.
    OpenOptions::new()
        .write(true)
        .open(&path)
        .unwrap()
        .set_len(bytes_at_2)
        .unwrap();

    // Reopen: recovered head 2 is BELOW the watermark 4 -> refused.
    let err = match BrokerLog::open_encrypted_verified(&path, KEY) {
        Ok(_) => panic!("a rolled-back log must be refused"),
        Err(e) => e,
    };
    assert!(
        err.to_string().contains("rolled back") || err.to_string().contains("below"),
        "the error must name the rollback: {err}"
    );
}

#[test]
fn normal_reopen_recovers_and_advances_the_watermark() {
    let (_tmp, path) = tmp("ok");
    cleanup(&path);
    {
        let mut log = BrokerLog::open_encrypted_verified_init(&path, KEY).unwrap();
        for i in 1..=3u64 {
            log.publish(1, i, "/a/x".into(), format!("m{i}").into_bytes())
                .unwrap();
        }
    }
    // Reopen twice: each verifies head == watermark and recovers everything.
    for _ in 0..2 {
        let log = BrokerLog::open_encrypted_verified(&path, KEY).unwrap();
        assert_eq!(log.read_from(Offset(0)).len(), 3);
    }
}

#[test]
fn a_deleted_watermark_is_refused_then_reinitializable() {
    let (_tmp, path) = tmp("deleted");
    cleanup(&path);
    {
        let mut log = BrokerLog::open_encrypted_verified_init(&path, KEY).unwrap();
        log.publish(1, 1, "/a/x".into(), b"data".to_vec()).unwrap();
    }
    // Attacker deletes the watermark to strip anti-rollback.
    std::fs::remove_file(hw_path(&path)).unwrap();
    assert!(
        BrokerLog::open_encrypted_verified(&path, KEY).is_err(),
        "a missing watermark on a non-empty log must be refused"
    );
    // The operator can knowingly re-establish it.
    let log = BrokerLog::open_encrypted_verified_init(&path, KEY).unwrap();
    assert_eq!(log.read_from(Offset(0)).len(), 1);
}

#[test]
fn a_tampered_watermark_is_refused() {
    let (_tmp, path) = tmp("tamper");
    cleanup(&path);
    {
        let mut log = BrokerLog::open_encrypted_verified_init(&path, KEY).unwrap();
        log.publish(1, 1, "/a/x".into(), b"data".to_vec()).unwrap();
    }
    // Flip a byte in the watermark sidecar -> its AEAD tag no longer verifies.
    let hw = hw_path(&path);
    let mut bytes = std::fs::read(&hw).unwrap();
    bytes[0] ^= 0x01;
    std::fs::write(&hw, &bytes).unwrap();
    assert!(
        BrokerLog::open_encrypted_verified(&path, KEY).is_err(),
        "a tampered watermark must be refused"
    );
}

#[test]
fn a_foreign_same_key_watermark_is_rejected() {
    // Cross-log splice (the audit's high finding): two logs under the SAME key. An
    // attacker truncates logA to hide records, then overwrites logA's watermark with a
    // DIFFERENT same-key log's watermark (a lower head that would mask the rollback).
    // The per-log identity bound into the watermark must reject it.
    let (_tmp_a, path_a) = tmp("splice_a");
    let (_tmp_b, path_b) = tmp("splice_b");
    cleanup(&path_a);
    cleanup(&path_b);

    // logB: a fresh same-key log at head 1 (its watermark carries logB's identity).
    {
        let mut b = BrokerLog::open_encrypted_verified_init(&path_b, KEY).unwrap();
        b.publish(1, 1, "/a/x".into(), b"b-one".to_vec()).unwrap();
    }
    // logA at head 1, note its byte length, then grow it to 3.
    {
        let mut a = BrokerLog::open_encrypted_verified_init(&path_a, KEY).unwrap();
        a.publish(1, 1, "/a/x".into(), b"a-one".to_vec()).unwrap();
    }
    let bytes_a1 = std::fs::metadata(&path_a).unwrap().len();
    {
        let mut a = BrokerLog::open_encrypted_verified(&path_a, KEY).unwrap();
        a.publish(1, 2, "/a/x".into(), b"a-two".to_vec()).unwrap();
        a.publish(1, 3, "/a/x".into(), b"a-three-acked".to_vec())
            .unwrap();
    }

    // Attack: truncate logA back to head 1 and splice logB's (same-key) watermark on.
    OpenOptions::new()
        .write(true)
        .open(&path_a)
        .unwrap()
        .set_len(bytes_a1)
        .unwrap();
    std::fs::copy(hw_path(&path_b), hw_path(&path_a)).unwrap();

    assert!(
        BrokerLog::open_encrypted_verified(&path_a, KEY).is_err(),
        "a foreign (same-key) watermark must be rejected"
    );
}
