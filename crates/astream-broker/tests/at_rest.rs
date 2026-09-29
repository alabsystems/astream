//! Evidence for `broker.log-encrypted-at-rest`: the durable log — a verbatim
//! recording of every published keystroke and screen frame — is sealed on disk
//! under a key, so a reader of the file recovers nothing without it, recovery with
//! the RIGHT key is lossless and exactly-once, a WRONG key is refused rather than
//! silently discarding data, and a CRC-valid tamper is caught by the AEAD tag.
#![cfg(feature = "at-rest")]

use astream_broker::BrokerLog;
use astream_wire::{Frame, Offset};
use std::sync::atomic::{AtomicU64, Ordering};

static CTR: AtomicU64 = AtomicU64::new(0);
const KEY: [u8; 32] = [0x5a; 32];

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
    let path = std::env::temp_dir().join(format!("asatrest_{tag}_{pid}_{n}.log"));
    (Cleanup::new(&[&path]), path)
}

fn contains(haystack: &[u8], needle: &[u8]) -> bool {
    haystack.windows(needle.len()).any(|w| w == needle)
}

#[test]
fn encrypts_on_disk_and_recovers_losslessly() {
    let (_tmp, path) = tmp("ok");
    let _ = std::fs::remove_file(&path);

    // Write two sensitive records under encryption, then close the log.
    {
        let mut log = BrokerLog::open_encrypted(&path, KEY).unwrap();
        assert_eq!(
            log.publish(
                1,
                1,
                "/a/stream/term/s1/out".into(),
                b"TOPSECRET-keystrokes".to_vec()
            )
            .unwrap(),
            (Offset(0), false)
        );
        log.publish(
            1,
            2,
            "/a/stream/term/s1/out".into(),
            b"more-secret-output".to_vec(),
        )
        .unwrap();
    }

    // The forensic content is gone from the raw file: neither the bodies nor the
    // subject appear in cleartext.
    let raw = std::fs::read(&path).unwrap();
    assert!(
        !contains(&raw, b"TOPSECRET-keystrokes"),
        "body leaked to disk"
    );
    assert!(
        !contains(&raw, b"more-secret-output"),
        "body leaked to disk"
    );
    assert!(
        !contains(&raw, b"/a/stream/term/s1/out"),
        "subject leaked to disk"
    );

    // Reopen with the same key: full, ordered recovery; exactly-once holds (a
    // re-publish of (1,1) dedups to its original offset).
    {
        let mut log = BrokerLog::open_encrypted(&path, KEY).unwrap();
        let recs = log.read_from(Offset(0));
        assert_eq!(recs.len(), 2);
        assert_eq!(recs[0].subject, "/a/stream/term/s1/out");
        assert_eq!(recs[0].body, b"TOPSECRET-keystrokes");
        assert_eq!(recs[1].body, b"more-secret-output");
        assert_eq!(
            log.publish(1, 1, "x".into(), b"dup".to_vec()).unwrap(),
            (Offset(0), true)
        );
    }
}

#[test]
fn wrong_key_is_refused_not_destroyed() {
    let (_tmp, path) = tmp("wrongkey");
    let _ = std::fs::remove_file(&path);
    {
        let mut log = BrokerLog::open_encrypted(&path, KEY).unwrap();
        log.publish(1, 1, "/a/x".into(), b"data".to_vec()).unwrap();
    }

    let mut wrong = KEY;
    wrong[0] ^= 0xff;
    // A wrong key must be REFUSED — never a silent truncation that would let the
    // broker start fresh and overwrite the (still-encrypted) data.
    assert!(
        BrokerLog::open_encrypted(&path, wrong).is_err(),
        "a wrong key must be refused"
    );
    // The file is untouched: the right key still recovers everything.
    let log = BrokerLog::open_encrypted(&path, KEY).unwrap();
    assert_eq!(log.read_from(Offset(0)).len(), 1);
}

#[test]
fn a_crc_valid_tamper_is_caught_by_the_aead_tag() {
    let (_tmp, path) = tmp("tamper");
    let _ = std::fs::remove_file(&path);
    {
        let mut log = BrokerLog::open_encrypted(&path, KEY).unwrap();
        log.publish(1, 1, "/a/x".into(), b"authentic".to_vec())
            .unwrap();
    }

    // Flip a byte inside the SEALED payload and RE-FRAME it, so the CRC is valid
    // again — the torn-tail check passes and only the AEAD tag can catch this.
    let raw = std::fs::read(&path).unwrap();
    let d = Frame::decode(&raw).unwrap().unwrap();
    let mut payload = d.frame.payload.clone();
    payload[0] ^= 0x01; // corrupt the nonce -> tag verification will fail
    let reframed = Frame::new(payload).encode().unwrap();
    std::fs::write(&path, &reframed).unwrap();

    // The frame decodes (CRC ok) but the record fails to authenticate -> refused.
    assert!(
        BrokerLog::open_encrypted(&path, KEY).is_err(),
        "a CRC-valid tamper must be caught by the AEAD tag"
    );
}

#[test]
fn plaintext_log_still_round_trips_and_is_readable() {
    // The scan-returns-Result refactor must not change the default (unencrypted)
    // path: a plaintext log round-trips, and its body IS visible on disk (the
    // contrast that makes the encryption meaningful).
    let (_tmp, path) = tmp("plain");
    let _ = std::fs::remove_file(&path);
    {
        let mut log = BrokerLog::open(&path).unwrap();
        log.publish(1, 1, "/a/x".into(), b"cleartext-body".to_vec())
            .unwrap();
    }
    let log = BrokerLog::open(&path).unwrap();
    assert_eq!(log.read_from(Offset(0))[0].body, b"cleartext-body");
    let raw = std::fs::read(&path).unwrap();
    assert!(
        contains(&raw, b"cleartext-body"),
        "plaintext log should be readable on disk"
    );
}

#[test]
fn plain_open_on_an_encrypted_log_is_refused_not_wiped() {
    // Using the WRONG constructor (plain open, no key) on an encrypted log must NOT
    // scan-to-empty and set_len(0) it away — it is refused, and the data survives.
    let (_tmp, path) = tmp("noconstructor");
    let _ = std::fs::remove_file(&path);
    {
        let mut log = BrokerLog::open_encrypted(&path, KEY).unwrap();
        log.publish(1, 1, "/a/x".into(), b"precious".to_vec())
            .unwrap();
    }
    let before = std::fs::metadata(&path).unwrap().len();
    assert!(
        BrokerLog::open(&path).is_err(),
        "plain open of an encrypted log must be refused"
    );
    let after = std::fs::metadata(&path).unwrap().len();
    assert_eq!(
        before, after,
        "the encrypted log must not be truncated by a refused open"
    );
    // The right constructor still recovers it.
    let log = BrokerLog::open_encrypted(&path, KEY).unwrap();
    assert_eq!(log.read_from(Offset(0)).len(), 1);
}

#[test]
fn a_naive_crc_breaking_flip_is_refused_not_truncated() {
    // The case the adversarial audit caught: a PLAIN single-byte flip breaks the frame
    // CRC, so Frame::decode returns Err (complete-but-corrupt). That must NOT be
    // conflated with a torn tail and silently truncate the record AND its authentic
    // suffix — for an encrypted log it is a hard error.
    let (_tmp, path) = tmp("naiveflip");
    let _ = std::fs::remove_file(&path);
    {
        let mut log = BrokerLog::open_encrypted(&path, KEY).unwrap();
        log.publish(1, 1, "/a/x".into(), b"first".to_vec()).unwrap();
        log.publish(1, 2, "/a/x".into(), b"second-must-survive".to_vec())
            .unwrap();
    }
    // Flip a byte inside record 0's sealed payload (past the 12-byte frame header) —
    // this breaks the CRC without shortening the file.
    let mut raw = std::fs::read(&path).unwrap();
    let before = raw.len() as u64;
    raw[20] ^= 0x01;
    std::fs::write(&path, &raw).unwrap();

    assert!(
        BrokerLog::open_encrypted(&path, KEY).is_err(),
        "a CRC-breaking tamper must be refused, not treated as a torn tail"
    );
    assert_eq!(
        std::fs::metadata(&path).unwrap().len(),
        before,
        "the log must not be truncated by a refused open"
    );
}
