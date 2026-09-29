//! A subscription whose cursor is below the retention base, on a log that retains
//! nothing at or above that cursor, PARKS until a record arrives — it must not spin.
//!
//! The tail parks while `head <= cursor`. Retention prunes the records below the
//! base, so a cursor below it can have `cursor < head` with nothing left to read:
//! the park predicate is false, the catch-up read is empty, and the loop retakes the
//! log lock as fast as it can. Records below the base are gone for good, so the tail
//! may move its cursor up to the base — which is what makes it park.

#![cfg(all(target_os = "linux", feature = "retention"))]

use astream_broker::{Broker, Client};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

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

fn tmp(tag: &str) -> String {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let p = format!("/tmp/ascore_tr_{tag}_{}_{n}", std::process::id());
    cleanup(&p);
    p
}

fn cleanup(p: &str) {
    for ext in ["", ".base", ".compact"] {
        let _ = std::fs::remove_file(format!("{p}{ext}"));
    }
}

/// This process's user + system CPU time, in clock ticks (`/proc/self/stat` fields
/// 14 and 15).
fn cpu_ticks() -> u64 {
    let stat = std::fs::read_to_string("/proc/self/stat").unwrap();
    // Fields after the parenthesised command name start at field 3 (state).
    let rest = &stat[stat.rfind(')').unwrap() + 2..];
    let f: Vec<&str> = rest.split_whitespace().collect();
    f[11].parse::<u64>().unwrap() + f[12].parse::<u64>().unwrap()
}

#[test]
fn a_subscriber_below_a_fully_retained_log_parks_instead_of_spinning() {
    let (log, sock) = (tmp("log"), tmp("sock"));
    let _tmp = Cleanup::new(&[&log, &sock]);
    let b = Broker::open(&log).unwrap();
    let mut h = b.serve(&sock).unwrap();
    let mut c = Client::connect(&sock).unwrap();
    for seq in 0..5 {
        c.publish(1, seq, "/t/x", b"m").unwrap();
    }
    assert_eq!(b.retain_before(5).unwrap(), 5, "everything retained away");

    let mut sub = Client::connect(&sock)
        .unwrap()
        .subscribe(0, "/t/>")
        .unwrap();
    // Let the connection thread reach its tail loop, then measure an idle second.
    std::thread::sleep(Duration::from_millis(200));
    let before = cpu_ticks();
    std::thread::sleep(Duration::from_secs(1));
    let used = cpu_ticks() - before;
    assert!(
        used < 25,
        "an idle subscription burned {used} clock ticks of CPU in one second"
    );

    // And it still delivers the next record, at its absolute offset.
    c.publish(1, 5, "/t/x", b"n").unwrap();
    let (off, subject, body) = sub.recv().unwrap().unwrap();
    assert_eq!(
        (off, subject.as_str(), body.as_slice()),
        (5, "/t/x", &b"n"[..])
    );

    drop(sub);
    drop(c);
    h.shutdown();
}
