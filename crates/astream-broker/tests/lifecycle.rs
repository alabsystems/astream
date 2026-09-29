//! Serve / shutdown lifecycle edges: what `serve` may remove at its socket path, and
//! which handle releases the log's exclusive lock when one broker serves two
//! endpoints.

#![cfg(unix)]

use astream_broker::{Broker, Client};
use std::io::ErrorKind;
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

fn tmp(tag: &str) -> String {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let p = format!("/tmp/ascore_lc_{tag}_{}_{n}", std::process::id());
    let _ = std::fs::remove_file(&p);
    p
}

/// `serve` unlinks a STALE socket (one nobody answers on) so a crashed broker's
/// leftover does not block a restart. A path that is not a socket at all — a typo'd
/// argument naming a regular file — is not a leftover of anything, and must survive.
#[test]
fn serve_refuses_to_replace_a_file_that_is_not_a_socket() {
    let (log, sock) = (tmp("log"), tmp("sock"));
    let _tmp = Cleanup::new(&[&log, &sock]);
    std::fs::write(&sock, b"not a socket").unwrap();
    let b = Broker::open(&log).unwrap();
    let err = b
        .serve(&sock)
        .err()
        .expect("serve bound over a regular file");
    assert_eq!(err.kind(), ErrorKind::AlreadyExists, "{err}");
    assert_eq!(std::fs::read(&sock).unwrap(), b"not a socket");

    // A stale SOCKET is still taken over.
    let _ = std::fs::remove_file(&sock);
    drop(std::os::unix::net::UnixListener::bind(&sock).unwrap()); // leaves the file
    let mut h = b.serve(&sock).expect("a stale socket is taken over");
    Client::connect(&sock)
        .unwrap()
        .publish(1, 0, "/t/x", b"m")
        .unwrap();
    h.shutdown();
}

/// One broker served on two endpoints hands its writer to the FIRST handle. Shutting
/// the other one down must not release the log's lock while that writer — the only
/// mutator — can still append: a second broker could then open the same log.
#[test]
fn only_the_handle_owning_the_writer_releases_the_log_lock() {
    let (log, sock) = (tmp("log"), tmp("sock"));
    let _tmp = Cleanup::new(&[&log, &sock]);
    let b = Broker::open(&log).unwrap();
    let mut unix = b.serve(&sock).unwrap();
    let mut tcp = b.serve_tcp("127.0.0.1:0").unwrap();
    Client::connect(&sock)
        .unwrap()
        .publish(1, 0, "/t/x", b"m")
        .unwrap();

    tcp.shutdown();
    let second = Broker::open(&log);
    assert!(
        second.is_err(),
        "the log was unlocked while the writer that owns it was still running"
    );

    unix.shutdown();
    let reopened = Broker::open(&log).expect("reopenable once the writer is joined");
    assert_eq!(reopened.head(), 1);
    drop(reopened);
    drop(b);
}
