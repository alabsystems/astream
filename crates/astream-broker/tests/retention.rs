//! Evidence for `broker.log-retention`: an explicit compaction drops records below a
//! floor offset while keeping surviving offsets ABSOLUTE (a consumer at a kept offset
//! is unaffected), survives a reopen, and composes with at-rest encryption and the
//! anti-rollback watermark.
#![cfg(feature = "retention")]

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
    let path = std::env::temp_dir().join(format!("asret_{tag}_{pid}_{n}.log"));
    (Cleanup::new(&[&path]), path)
}

fn cleanup(log: &std::path::Path) {
    for ext in ["", ".base", ".hw", ".compact"] {
        let mut s = log.as_os_str().to_os_string();
        s.push(ext);
        let _ = std::fs::remove_file(std::path::PathBuf::from(s));
    }
}

fn fill(log: &mut BrokerLog, n: u64) {
    for i in 0..n {
        log.publish(1, i, "/a/stream/x".into(), format!("m{i}").into_bytes())
            .unwrap();
    }
}

#[test]
fn retain_drops_old_records_keeping_absolute_offsets() {
    let (_tmp, path) = tmp("plain");
    cleanup(&path);
    {
        let mut log = BrokerLog::open(&path).unwrap();
        fill(&mut log, 5); // offsets 0..4
        assert_eq!(log.base(), Offset(0));

        let dropped = log.retain_before(Offset(3)).unwrap();
        assert_eq!(dropped, 3, "records 0,1,2 dropped");
        assert_eq!(log.base(), Offset(3));

        let recs = log.read_from(Offset(0));
        assert_eq!(recs.len(), 2, "only the retained suffix remains");
        assert_eq!(recs[0].seq, Offset(3), "kept offsets are ABSOLUTE");
        assert_eq!(recs[1].seq, Offset(4));
        assert_eq!(&recs[0].body, b"m3");
        // A consumer above the floor is exact; one below it catches up at the floor.
        assert_eq!(log.read_from(Offset(4)).len(), 1);
        assert_eq!(log.read_from(Offset(1)).len(), 2);

        // Idempotent / clamped: a floor at or below the base drops nothing.
        assert_eq!(log.retain_before(Offset(3)).unwrap(), 0);
        assert_eq!(log.retain_before(Offset(0)).unwrap(), 0);
    }
    // Reopen: the base floor and the absolute offsets are recovered.
    {
        let log = BrokerLog::open(&path).unwrap();
        assert_eq!(log.base(), Offset(3));
        assert_eq!(log.head(), Offset(5));
        let recs = log.read_from(Offset(0));
        assert_eq!(recs.len(), 2);
        assert_eq!(recs[0].seq, Offset(3));
        assert_eq!(&recs[1].body, b"m4");
    }
}

#[cfg(feature = "at-rest")]
#[test]
fn retention_on_an_encrypted_log_recovers_the_kept_suffix() {
    const KEY: [u8; 32] = [0x7e; 32];
    let (_tmp, path) = tmp("enc");
    cleanup(&path);
    {
        let mut log = BrokerLog::open_encrypted(&path, KEY).unwrap();
        fill(&mut log, 5);
        assert_eq!(log.retain_before(Offset(2)).unwrap(), 2);
    }
    // The kept records were sealed under their ORIGINAL offset AADs; recovery with the
    // recovered base (2) decrypts them at 2,3,4.
    {
        let log = BrokerLog::open_encrypted(&path, KEY).unwrap();
        assert_eq!(log.base(), Offset(2));
        let recs = log.read_from(Offset(0));
        assert_eq!(recs.len(), 3);
        assert_eq!(recs[0].seq, Offset(2));
        assert_eq!(&recs[0].body, b"m2");
    }
}

#[cfg(feature = "anti-rollback")]
#[test]
fn retention_reidentifies_the_anti_rollback_watermark() {
    const KEY: [u8; 32] = [0x2b; 32];
    let (_tmp, path) = tmp("roll");
    cleanup(&path);
    {
        let mut log = BrokerLog::open_encrypted_verified_init(&path, KEY).unwrap();
        fill(&mut log, 5);
        // Retention changes the FIRST record (the log's identity); retain_before must
        // re-write the watermark so a later verified open still accepts the log.
        assert_eq!(log.retain_before(Offset(2)).unwrap(), 2);
    }
    let log = BrokerLog::open_encrypted_verified(&path, KEY)
        .expect("a retained log must still pass anti-rollback verification");
    assert_eq!(log.base(), Offset(2));
    assert_eq!(log.head(), Offset(5));
}

#[cfg(feature = "anti-rollback")]
#[test]
fn a_tampered_retention_base_is_refused_under_anti_rollback() {
    // The `<log>.base` sidecar is plaintext, but under anti-rollback it is BOUND into
    // the authenticated watermark (and, for an encrypted log, the record AADs depend on
    // it), so tampering it to reindex/hide records is refused.
    const KEY: [u8; 32] = [0x9d; 32];
    let (_tmp, path) = tmp("basetamper");
    cleanup(&path);
    {
        let mut log = BrokerLog::open_encrypted_verified_init(&path, KEY).unwrap();
        fill(&mut log, 5);
        assert_eq!(log.retain_before(Offset(2)).unwrap(), 2);
    }
    // Overwrite the base sidecar with a different value.
    let base_p = {
        let mut s = path.as_os_str().to_os_string();
        s.push(".base");
        std::path::PathBuf::from(s)
    };
    std::fs::write(&base_p, 0u64.to_le_bytes()).unwrap();
    assert!(
        BrokerLog::open_encrypted_verified(&path, KEY).is_err(),
        "a tampered retention base must be refused under anti-rollback"
    );
}
