//! A Replicated leader whose log retention has compacted past a LAGGING follower's
//! confirmed prefix keeps replicating to the followers that are caught up.
//!
//! The leader re-ships each batch from the lowest live follower prefix, and
//! `read_from` clamps a request below the retention base up to the first retained
//! record. The slice it hands back therefore starts ABOVE the offset that was asked
//! for, and each follower's position in it has to be measured from the slice's own
//! first record — or a caught-up follower is handed nothing (or the wrong records),
//! and every publish is refused "not replicated to quorum".

#![cfg(all(unix, feature = "retention"))]

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
    let pid = std::process::id();
    let p = format!("/tmp/ascore_rr_{tag}_{pid}_{n}");
    cleanup(&p);
    p
}

fn cleanup(p: &str) {
    for ext in ["", ".base", ".compact", ".replica"] {
        let _ = std::fs::remove_file(format!("{p}{ext}"));
    }
}

#[test]
fn a_follower_lagging_below_the_retention_base_does_not_stall_the_caught_up_one() {
    let (f1_log, f2_log, l_log, l_sock) = (tmp("f1"), tmp("f2"), tmp("l"), tmp("sock"));
    let _tmp = Cleanup::new(&[&f1_log, &f2_log, &l_log, &l_sock]);

    let f1 = Broker::open(&f1_log).unwrap();
    let mut f1h = f1.serve_tcp("127.0.0.1:0").unwrap();
    let f2 = Broker::open(&f2_log).unwrap();
    let mut f2h = f2.serve_tcp("127.0.0.1:0").unwrap();
    let followers = vec![
        f1h.tcp_addr().unwrap().to_string(),
        f2h.tcp_addr().unwrap().to_string(),
    ];

    let leader =
        Broker::open_replicated_with(&l_log, &followers, 1, Duration::from_millis(500)).unwrap();
    let mut lh = leader.serve(&l_sock).unwrap();
    let mut c = Client::connect(&l_sock).unwrap();

    for seq in 0..10 {
        assert_eq!(c.publish(1, seq, "/t/x", b"m").unwrap().0, seq);
    }
    assert_eq!(f2.head(), 10, "both followers confirmed the first ten");

    // Follower 2 goes away: its confirmed prefix stays at 10 while follower 1 (a
    // quorum of one) keeps confirming.
    f2h.shutdown();
    drop(f2);
    for seq in 10..20 {
        assert_eq!(c.publish(1, seq, "/t/x", b"m").unwrap().0, seq);
    }
    assert_eq!(f1.head(), 20);

    // Compact the leader past follower 2's prefix (but not follower 1's).
    assert_eq!(leader.retain_before(15).unwrap(), 15);

    // Follower 1 lacks nothing below the base: the next record must reach it.
    let ack = c.publish(1, 20, "/t/x", b"m");
    assert_eq!(
        ack.as_ref().map(|a| a.0).map_err(|e| e.to_string()),
        Ok(20),
        "a follower below the retention base stalled replication to the caught-up one"
    );
    assert_eq!(f1.head(), 21, "the caught-up follower holds the new record");

    drop(c);
    lh.shutdown();
    f1h.shutdown();
}
