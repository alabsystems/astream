//! Evidence for `broker.pipelining`: SINGLE-CONNECTION pipelining — one connection with
//! many publishes in flight — preserves ordering, durability, and exactly-once ingest.
//! The broker streams acks back IN ORDER on a cloned write half while it keeps reading,
//! so the in-flight publishes coalesce into group-commit fsyncs (one connection
//! saturates the writer) at the SAME `ack ⟹ fsync'd` guarantee. No sleeps.

#![cfg(unix)] // serves the broker on a Unix-domain socket; std has no UDS on Windows

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
fn single_connection_pipelined_publishes_ordered_durable_exactly_once() {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = format!("/tmp/aspipe_t_{pid}_{n}.log");
    let sock = format!("/tmp/aspipe_t_{pid}_{n}.sock");
    let _ = std::fs::remove_file(&log);
    let _tmp = Cleanup::new(&[&log, &sock]);

    const N: usize = 500;
    let owned: Vec<Vec<u8>> = (0..N).map(|i| format!("m{i}").into_bytes()).collect();
    let bodies: Vec<&[u8]> = owned.iter().map(|v| v.as_slice()).collect();

    {
        let b = Broker::open(&log).unwrap();
        let _h = b.serve(&sock).unwrap();

        let mut c = Client::connect(&sock).unwrap();
        // Many publishes in flight on ONE connection (window 128).
        let acks = c.publish_pipelined(1, "/a/p/x", &bodies, 128).unwrap();
        assert_eq!(acks.len(), N, "every pipelined publish acked");
        for (i, (off, deduped)) in acks.iter().enumerate() {
            assert_eq!(*off, i as u64, "acks stream back in request order");
            assert!(!deduped, "a first send is never a dup");
        }
        // Re-pipeline the SAME (producer_id, seqs): exactly-once ingest → every one is
        // deduped to its ORIGINAL offset and nothing is re-appended, even pipelined.
        let acks2 = c.publish_pipelined(1, "/a/p/x", &bodies, 128).unwrap();
        for (i, (off, deduped)) in acks2.iter().enumerate() {
            assert_eq!(
                (*off, *deduped),
                (i as u64, true),
                "pipelined re-send is deduped to the original offset"
            );
        }
        // Subscribe on the SAME connection: drives the finish-pipeline transition (flush
        // all pending acks, reclaim the socket, then stream). Records arrive in dense
        // offset order [0, N).
        let mut sub = c.subscribe(0, "/a/p/>").unwrap();
        for (i, body) in owned.iter().enumerate() {
            let (off, _s, got) = sub.recv().unwrap().unwrap();
            assert_eq!(off, i as u64, "delivered in offset order");
            assert_eq!(&got, body, "body intact");
        }
    } // drop handle → shutdown

    // Restart: every pipelined-and-acked record is durable and re-delivered in order.
    let b2 = Broker::open(&log).unwrap();
    let _h2 = b2.serve(&sock).unwrap();
    let mut sub = Client::connect(&sock)
        .unwrap()
        .subscribe(0, "/a/p/>")
        .unwrap();
    for i in 0..N {
        let (off, _s, _b) = sub.recv().unwrap().unwrap();
        assert_eq!(off, i as u64, "all {N} recovered after restart, in order");
    }
}

/// Regression: a producer connection that publishes then sits IDLE (its read half
/// parked in the broker, plus a spawned ack-writer thread) must be force-reaped on
/// broker shutdown — not left hanging until the client happens to act. The client is
/// deliberately kept ALIVE across shutdown; if shutdown failed to close the connection
/// socket, the broker's acceptor/writer join could stall and this test would hang.
#[test]
fn shutdown_reaps_an_idle_pipelined_connection() {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = format!("/tmp/aspipe_sd_{pid}_{n}.log");
    let sock = format!("/tmp/aspipe_sd_{pid}_{n}.sock");
    let _ = std::fs::remove_file(&log);
    let _tmp = Cleanup::new(&[&log, &sock]);

    let b = Broker::open(&log).unwrap();
    let mut h = b.serve(&sock).unwrap();
    // A producer connection that publishes (starting its ack-writer) then idles.
    let mut c = Client::connect(&sock).unwrap();
    c.publish(1, 1, "/a/p/x", b"hello").unwrap();
    // Do NOT drop `c`: the connection stays open and idle. shutdown() must still return
    // promptly by force-closing the socket (reaping the read + ack-writer threads).
    h.shutdown();
    // Reaching here means shutdown did not hang on the live idle connection.
    drop(c);
}
