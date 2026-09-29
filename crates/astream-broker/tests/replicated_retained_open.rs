//! A leader log that retention has compacted opens in the Replicated tier.
//!
//! After `retain_before` the log's first record is above offset 0, and nothing below
//! it exists to ship. Each follower link's confirmed prefix therefore starts at the
//! log's BASE: a follower that holds the retained records confirms them at open and
//! replication carries on. A follower BEHIND the base lacks records the leader no
//! longer has, so it can never be caught up: it answers with a gap and is left
//! behind — never shipped to again, counting toward no quorum above what it holds —
//! exactly as a follower whose prefix retention pruned past while the leader ran.

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
const IO: Duration = Duration::from_millis(500);

fn tmp(tag: &str) -> String {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let p = format!("/tmp/ascore2_rro_{tag}_{pid}_{n}");
    cleanup(&p);
    p
}

fn cleanup(p: &str) {
    for ext in ["", ".base", ".compact", ".replica"] {
        let _ = std::fs::remove_file(format!("{p}{ext}"));
    }
}

/// Write records 0..20 through a Replicated leader at `l_log` whose follower is
/// `follower`, then compact the leader's log to [15, 20) and close it.
fn retained_leader_log(l_log: &str, follower: &str) {
    let sock = tmp("sock");
    let _tmp = Cleanup::new(&[&sock]);
    let leader = Broker::open_replicated_with(l_log, &[follower.to_string()], 1, IO).unwrap();
    let mut h = leader.serve(&sock).unwrap();
    let mut c = Client::connect(&sock).unwrap();
    for seq in 0..20 {
        assert_eq!(c.publish(1, seq, "/t/x", b"m").unwrap().0, seq);
    }
    assert_eq!(leader.retain_before(15).unwrap(), 15);
    drop(c);
    h.shutdown();
    drop(leader);
}

#[test]
fn a_retained_leader_log_opens_replicated_and_keeps_replicating() {
    let (f_log, l_log, sock) = (tmp("f"), tmp("l"), tmp("sock"));
    let _tmp = Cleanup::new(&[&f_log, &l_log, &sock]);
    let f = Broker::open(&f_log).unwrap();
    let mut fh = f.serve_tcp("127.0.0.1:0").unwrap();
    let f_addr = fh.tcp_addr().unwrap().to_string();
    retained_leader_log(&l_log, &f_addr);
    assert_eq!(f.head(), 20);

    let leader = Broker::open_replicated_with(&l_log, &[f_addr], 1, IO)
        .expect("a leader log compacted by retention did not open replicated");
    assert_eq!(
        leader.visible_head(),
        20,
        "the follower confirmed the retained log"
    );
    let mut lh = leader.serve(&sock).unwrap();
    let mut c = Client::connect(&sock).unwrap();
    assert_eq!(c.publish(1, 20, "/t/x", b"n").unwrap(), (20, false));
    assert_eq!(f.head(), 21, "the follower holds the new record");

    // Leader-side delivery starts at the base, at absolute offsets.
    let mut sub = Client::connect(&sock)
        .unwrap()
        .subscribe(0, "/t/>")
        .unwrap();
    for want in 15..21 {
        assert_eq!(sub.recv().unwrap().unwrap().0, want);
    }

    drop(sub);
    drop(c);
    lh.shutdown();
    fh.shutdown();
}

#[test]
fn a_follower_behind_the_retained_base_is_left_behind() {
    let (f1_log, f2_log, l_log, sock) = (tmp("f1"), tmp("f2"), tmp("l"), tmp("sock"));
    let _tmp = Cleanup::new(&[&f1_log, &f2_log, &l_log, &sock]);
    let f1 = Broker::open(&f1_log).unwrap();
    let mut f1h = f1.serve_tcp("127.0.0.1:0").unwrap();
    let f1_addr = f1h.tcp_addr().unwrap().to_string();
    retained_leader_log(&l_log, &f1_addr);

    // Follower 2 is empty: records 0..15, which it lacks, exist nowhere on the leader.
    let f2 = Broker::open(&f2_log).unwrap();
    let mut f2h = f2.serve_tcp("127.0.0.1:0").unwrap();
    let followers = vec![f1_addr, f2h.tcp_addr().unwrap().to_string()];

    // A quorum it would have to be part of cannot be met, and says so at open.
    let err = match Broker::open_replicated_with(&l_log, &followers, 2, IO) {
        Ok(_) => panic!("a quorum of 2 opened with a follower that can never be caught up"),
        Err(e) => e.to_string(),
    };
    assert!(err.contains("quorum"), "{err}");

    // A quorum of one: follower 1 carries it, follower 2 is left where it is.
    let leader = Broker::open_replicated_with(&l_log, &followers, 1, IO).expect(
        "a follower behind the retained base failed the open for a quorum it is not needed for",
    );
    let mut lh = leader.serve(&sock).unwrap();
    let mut c = Client::connect(&sock).unwrap();
    for seq in 20..23 {
        assert_eq!(c.publish(1, seq, "/t/x", b"n").unwrap().0, seq);
    }
    assert_eq!(f1.head(), 23);
    assert_eq!(
        f2.head(),
        0,
        "nothing reached the follower that cannot hold it"
    );

    drop(c);
    lh.shutdown();
    f1h.shutdown();
    f2h.shutdown();
}
