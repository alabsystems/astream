//! A connection refused at the connection cap is TOLD so: the client reads the
//! broker's "too many connections" error, whether its first request was sent
//! before or after the refusal, instead of a bare broken pipe or reset.

#![cfg(unix)]

use astream_broker::proto::{decode_response, read_frame};
use astream_broker::{Broker, Client, Response};
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

fn paths() -> (Cleanup, String, String) {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = format!("/tmp/ascore_cc_{pid}_{n}.log");
    let _ = std::fs::remove_file(&log);
    let sock = format!("/tmp/ascore_cc_{pid}_{n}.sock");
    (Cleanup::new(&[&log, &sock]), log, sock)
}

fn assert_refusal(err: std::io::Error, what: &str) {
    assert!(
        err.to_string().contains("too many connections"),
        "{what}: the refused client saw {err:?}, not the refusal"
    );
}

#[test]
fn a_client_refused_at_the_connection_cap_reads_why() {
    let (_tmp, log, sock) = paths();
    let b = Broker::open(&log).unwrap();
    b.set_max_conns(1);
    let mut uds = b.serve(&sock).unwrap();
    let mut tcp = b.serve_tcp("127.0.0.1:0").unwrap();
    let addr = tcp.tcp_addr().unwrap().to_string();

    // The one allowed connection, registered (it has been answered).
    let mut held = Client::connect(&sock).unwrap();
    held.publish(1, 0, "/a/x", b"held").unwrap();

    for i in 0..10 {
        // Request written at once, racing the broker's refusal.
        let err = Client::connect(&sock)
            .unwrap()
            .publish(2, i, "/a/x", b"m")
            .unwrap_err();
        assert_refusal(err, "unix, immediate");
        let err = Client::connect_tcp(&addr)
            .unwrap()
            .publish(2, i, "/a/x", b"m")
            .unwrap_err();
        assert_refusal(err, "tcp, immediate");
    }
    // Request written only after the refusal has certainly been sent.
    for connect in 0..2 {
        let err = if connect == 0 {
            let mut c = Client::connect(&sock).unwrap();
            std::thread::sleep(std::time::Duration::from_millis(100));
            c.publish(2, 100, "/a/x", b"m").unwrap_err()
        } else {
            let mut c = Client::connect_tcp(&addr).unwrap();
            std::thread::sleep(std::time::Duration::from_millis(100));
            c.publish(2, 100, "/a/x", b"m").unwrap_err()
        };
        assert_refusal(err, "late request");
    }

    // A refused client that keeps reading sees EOF right after the refusal, not
    // after the broker's linger.
    let mut raw = std::os::unix::net::UnixStream::connect(&sock).unwrap();
    let t = std::time::Instant::now();
    let first = read_frame(&mut raw).unwrap().expect("the refusal");
    assert!(matches!(
        decode_response(&first),
        Some(Response::Error { code: 6, .. })
    ));
    assert_eq!(read_frame(&mut raw).unwrap(), None, "EOF after the refusal");
    assert!(
        t.elapsed() < std::time::Duration::from_millis(400),
        "EOF waited out the linger: {:?}",
        t.elapsed()
    );

    drop(held);
    uds.shutdown();
    tcp.shutdown();
}
