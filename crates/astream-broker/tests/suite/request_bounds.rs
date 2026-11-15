//! Names a request carries — subjects, filters, group names, cursors, grants — are
//! bounded, and refused with an ordinary error before anything parses them.
//!
//! The frame cap alone (16 MiB) lets one cheap request name a 16 MiB subject or
//! filter, and parsing and matching it costs many times its size (a filter's
//! segments, a subject's segment vector per keyring entry). A bounded name keeps
//! every such cost small; the connection stays usable after the refusal.

#![cfg(unix)]

use astream_broker::broker::MAX_NAME_LEN;
use astream_broker::{Broker, Client};
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

#[test]
fn oversized_names_are_refused_and_the_connection_stays_usable() {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = format!("/tmp/ascore_rb_{pid}_{n}.log");
    let sock = format!("/tmp/ascore_rb_{pid}_{n}.sock");
    let _ = std::fs::remove_file(&log);
    let _tmp = Cleanup::new(&[&log, &sock]);
    let b = Broker::open(&log).unwrap();
    let mut h = b.serve(&sock).unwrap();
    let mut c = Client::connect(&sock).unwrap();

    // Exactly at the bound is fine; one byte over is refused.
    let at = format!("/a/{}", "x".repeat(MAX_NAME_LEN - 3));
    assert_eq!(at.len(), MAX_NAME_LEN);
    c.publish(1, 0, &at, b"ok").unwrap();
    let over = format!("{at}y");

    let err = c.publish(1, 1, &over, b"no").unwrap_err().to_string();
    assert!(err.contains("too long"), "publish: {err}");
    let err = c.fetch(0, &over, 10).unwrap_err().to_string();
    assert!(err.contains("too long"), "fetch filter: {err}");
    let err = c.last(&over, "", 10).unwrap_err().to_string();
    assert!(err.contains("too long"), "last filter: {err}");
    let err = c.last("/a/>", &over, 10).unwrap_err().to_string();
    assert!(err.contains("too long"), "last cursor: {err}");
    let err = c.commit(&over, 0).unwrap_err().to_string();
    assert!(err.contains("too long"), "commit group: {err}");

    // Nothing was appended for the refused requests, and the connection still works.
    let (page, _) = c.fetch(0, "/a/>", 10).unwrap();
    assert_eq!(page.len(), 1);
    assert_eq!(c.publish(1, 2, "/a/y", b"after").unwrap().0, 1);

    drop(c);
    h.shutdown();
}
