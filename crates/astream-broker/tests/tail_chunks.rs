//! A subscriber catching up over a long log, and a fork snapshot of one, read the log
//! a bounded chunk at a time — releasing the log lock between chunks, so a reader
//! starting at offset 0 never stalls every publisher for a whole-log copy. What they
//! DELIVER must not change with it: every matching record, in offset order, exactly
//! once, across every chunk boundary and while new records land mid catch-up.

#![cfg(unix)]

use astream_broker::broker::TAIL_CHUNK;
use astream_broker::{Broker, Client, Durability, Event};
use std::sync::atomic::{AtomicU64, Ordering};

static CTR: AtomicU64 = AtomicU64::new(0);

/// More than two of the broker's catch-up chunks, and not a multiple of one.
const N: u64 = 2 * TAIL_CHUNK as u64 + 1808;

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

fn paths() -> (Cleanup, String, String) {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = format!("/tmp/ascore2_tc_{pid}_{n}.log");
    let _ = std::fs::remove_file(&log);
    let sock = format!("/tmp/ascore2_tc_{pid}_{n}.sock");
    (Cleanup::new(&[&log, &sock]), log, sock)
}

/// Subject of record `seq`: two lanes, so a filter can take every other record.
fn subject(seq: u64) -> &'static str {
    if seq.is_multiple_of(2) {
        "/t/even"
    } else {
        "/t/odd"
    }
}

fn fill(sock: &str, from: u64, to: u64) {
    let mut c = Client::connect(sock).unwrap();
    for seq in from..to {
        assert_eq!(
            c.publish(1, seq, subject(seq), &seq.to_le_bytes()).unwrap(),
            (seq, false)
        );
    }
}

#[test]
fn catch_up_across_chunks_delivers_every_record_once_in_order() {
    let (_tmp, log, sock) = paths();
    let b = Broker::open_with(&log, Durability::Relaxed).unwrap();
    let mut h = b.serve(&sock).unwrap();
    fill(&sock, 0, N);

    let mut all = Client::connect(&sock)
        .unwrap()
        .subscribe(0, "/t/>")
        .unwrap();
    let mut odd = Client::connect(&sock)
        .unwrap()
        .subscribe(1, "/t/odd")
        .unwrap();
    // More records land while both catch up.
    let writer = {
        let sock = sock.clone();
        std::thread::spawn(move || fill(&sock, N, N + 500))
    };

    for want in 0..N + 500 {
        let (off, subj, body) = all.recv().unwrap().unwrap();
        assert_eq!(
            (off, subj.as_str(), body.as_slice()),
            (want, subject(want), &want.to_le_bytes()[..])
        );
    }
    for want in (1..N + 500).step_by(2) {
        let (off, subj, _) = odd.recv().unwrap().unwrap();
        assert_eq!((off, subj.as_str()), (want, "/t/odd"));
    }
    writer.join().unwrap();

    drop(all);
    drop(odd);
    h.shutdown();
}

#[test]
fn a_fork_snapshot_across_chunks_is_the_whole_counterfactual_history() {
    let (_tmp, log, sock) = paths();
    let b = Broker::open_with(&log, Durability::Relaxed).unwrap();
    let mut h = b.serve(&sock).unwrap();
    fill(&sock, 0, N);

    // Forked in the THIRD chunk, so the replacement is found after two lock releases.
    let fork_at = N - 7;
    let mut fork = Client::connect(&sock)
        .unwrap()
        .fork_subscribe(fork_at, "/t/odd", b"replaced", "/t/>")
        .unwrap();
    // Records that land after the fork's head are not part of its snapshot.
    fill(&sock, N, N + 10);

    let mut got = 0u64;
    loop {
        match fork.recv_event().unwrap() {
            Some(Event::Delivery {
                offset: off,
                subject: subj,
                body,
            }) => {
                assert_eq!(off, got, "a gap or a repeat in the fork snapshot");
                if off == fork_at {
                    assert_eq!(
                        (subj.as_str(), body.as_slice()),
                        ("/t/odd", &b"replaced"[..])
                    );
                } else {
                    assert_eq!(
                        (subj.as_str(), body.as_slice()),
                        (subject(off), &off.to_le_bytes()[..])
                    );
                }
                got += 1;
            }
            Some(Event::Mark { next, head }) => {
                assert_eq!((next, head), (N, N));
                break;
            }
            None => panic!("the fork ended without its end marker"),
        }
    }
    assert_eq!(got, N, "the snapshot is every record below its head");

    drop(fork);
    h.shutdown();
}

/// Over a log retention has compacted, both readers start at the base — an offset
/// in the middle of what would have been a chunk — keep absolute offsets, and a fork
/// below the base replaces nothing (the record it names is gone).
#[cfg(feature = "retention")]
#[test]
fn chunked_reads_start_at_the_retention_base() {
    let (_tmp, log, sock) = paths();
    let b = Broker::open_with(&log, Durability::Relaxed).unwrap();
    let mut h = b.serve(&sock).unwrap();
    fill(&sock, 0, N);
    let base = TAIL_CHUNK as u64 + 5;
    assert_eq!(b.retain_before(base).unwrap(), base);

    let mut sub = Client::connect(&sock)
        .unwrap()
        .subscribe(0, "/t/>")
        .unwrap();
    for want in base..N {
        assert_eq!(sub.recv().unwrap().unwrap().0, want);
    }

    for (fork_at, replaced) in [(base - 1, false), (base + 1, true)] {
        let mut fork = Client::connect(&sock)
            .unwrap()
            .fork_subscribe(fork_at, "/t/odd", b"replaced", "/t/>")
            .unwrap();
        let mut want = base;
        while let Some((off, _, body)) = fork.recv().unwrap() {
            assert_eq!(off, want);
            assert_eq!(body == b"replaced", replaced && off == fork_at);
            want += 1;
        }
        assert_eq!(want, N, "the fork snapshot is every retained record");
    }

    drop(sub);
    h.shutdown();
}
