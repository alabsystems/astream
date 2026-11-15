//! Evidence for `broker.identity-tcp-roundtrip`: Rung 8. Mutual static public-key
//! identity with NO shared secret — the SAME exactly-once pub/sub + resume works
//! over a signed-DH (SIGMA/Ed25519) transport where the client pins the broker's
//! host key and the broker allow-lists the client's identity. A wrong host key, an
//! unauthorized client, and a plaintext peer are all refused.
#![cfg(feature = "identity")]

use astream_broker::{Broker, Client, IdentityKeypair};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc;
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

fn log_path(tag: &str) -> (Cleanup, std::path::PathBuf) {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = std::env::temp_dir().join(format!("asid_{tag}_{pid}_{n}.log"));
    (Cleanup::new(&[&log]), log)
}

#[test]
fn mutual_identity_publish_subscribe_and_resume() {
    let (_tmp, log) = log_path("ok");
    let _ = std::fs::remove_file(&log);

    let server_id = IdentityKeypair::generate();
    let server_pub = server_id.public();
    let client_id = IdentityKeypair::generate();
    let client_pub = client_id.public();

    let broker = Broker::open(&log).unwrap();
    // The broker presents server_id and allow-lists the one client.
    let h = broker
        .serve_tcp_identity("127.0.0.1:0", server_id, vec![client_pub])
        .unwrap();
    let addr = h.tcp_addr().expect("a TCP endpoint").to_string();

    // The client pins the broker's host key and presents its own identity.
    let mut p = Client::connect_tcp_identity(&addr, client_id.clone(), server_pub).unwrap();
    for i in 1..=4u64 {
        let (off, dup) = p
            .publish(1, i, "/a/stream/x", format!("m{i}").as_bytes())
            .unwrap();
        assert_eq!((off, dup), (i - 1, false));
    }

    let mut sub = Client::connect_tcp_identity(&addr, client_id.clone(), server_pub)
        .unwrap()
        .subscribe(0, "/a/stream/>")
        .unwrap();
    let got: Vec<(u64, String, Vec<u8>)> = (0..4).map(|_| sub.recv().unwrap().unwrap()).collect();
    assert_eq!(got[0], (0, "/a/stream/x".to_string(), b"m1".to_vec()));
    assert_eq!(got[3].0, 3);

    drop(sub);
    let mut sub2 = Client::connect_tcp_identity(&addr, client_id.clone(), server_pub)
        .unwrap()
        .subscribe(2, "/a/stream/>")
        .unwrap();
    assert_eq!(
        sub2.recv().unwrap().unwrap(),
        (2, "/a/stream/x".to_string(), b"m3".to_vec())
    );

    assert_eq!(p.publish(1, 2, "/a/stream/x", b"m2").unwrap(), (1, true));
}

fn expect_refused<F>(what: &str, connect: F)
where
    F: FnOnce() -> std::io::Result<(u64, bool)> + Send + 'static,
{
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let _ = tx.send(connect().is_err());
    });
    match rx.recv_timeout(Duration::from_secs(5)) {
        Ok(errored) => assert!(errored, "{what} must be refused"),
        Err(_) => panic!("{what}: neither completed nor was refused within 5s"),
    }
}

#[test]
fn client_rejects_a_wrong_host_key() {
    let (_tmp, log) = log_path("wronghost");
    let _ = std::fs::remove_file(&log);
    let server_id = IdentityKeypair::generate();
    let client_id = IdentityKeypair::generate();
    let client_pub = client_id.public();
    let broker = Broker::open(&log).unwrap();
    let h = broker
        .serve_tcp_identity("127.0.0.1:0", server_id, vec![client_pub])
        .unwrap();
    let addr = h.tcp_addr().expect("a TCP endpoint").to_string();

    // Pin the WRONG host key.
    // A fresh random identity, which is (with overwhelming probability) not the
    // broker's host key.
    let wrong_host = IdentityKeypair::generate().public();
    let addr2 = addr.clone();
    expect_refused("a client pinning the wrong host key", move || {
        let mut c = Client::connect_tcp_identity(&addr2, client_id, wrong_host)?;
        c.publish(1, 1, "/a/stream/x", b"x")
    });
}

#[test]
fn server_rejects_an_unauthorized_client() {
    let (_tmp, log) = log_path("unauth");
    let _ = std::fs::remove_file(&log);
    let server_id = IdentityKeypair::generate();
    let server_pub = server_id.public();
    // Allow-list a DIFFERENT client, not the one that connects.
    let allowed = IdentityKeypair::generate().public();
    let broker = Broker::open(&log).unwrap();
    let h = broker
        .serve_tcp_identity("127.0.0.1:0", server_id, vec![allowed])
        .unwrap();
    let addr = h.tcp_addr().expect("a TCP endpoint").to_string();

    let stranger = IdentityKeypair::generate();
    expect_refused("an unauthorized client", move || {
        let mut c = Client::connect_tcp_identity(&addr, stranger, server_pub)?;
        c.publish(1, 1, "/a/stream/x", b"x")
    });
}

#[test]
fn plaintext_peer_is_refused() {
    let (_tmp, log) = log_path("plain");
    let _ = std::fs::remove_file(&log);
    let server_id = IdentityKeypair::generate();
    let client_pub = IdentityKeypair::generate().public();
    let broker = Broker::open(&log).unwrap();
    let h = broker
        .serve_tcp_identity("127.0.0.1:0", server_id, vec![client_pub])
        .unwrap();
    let addr = h.tcp_addr().expect("a TCP endpoint").to_string();
    expect_refused("a plaintext peer on an identity endpoint", move || {
        let mut c = Client::connect_tcp(&addr)?;
        c.publish(1, 1, "/a/stream/x", b"x")
    });
}
