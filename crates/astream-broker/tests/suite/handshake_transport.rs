//! Evidence for `broker.handshake-tcp-roundtrip`: Rung 7. The SAME exactly-once
//! pub/sub + resume works over a FORWARD-SECRET transport — each connection first
//! runs an ephemeral-X25519 key agreement authenticated by the pre-shared key, so
//! the per-session key is fresh and a later PSK compromise cannot decrypt past
//! traffic. A wrong PSK and a plaintext (non-handshake) peer are both refused.
#![cfg(feature = "handshake")]

use astream_broker::{Broker, Client};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc;
use std::time::Duration;

static CTR: AtomicU64 = AtomicU64::new(0);

const PSK: [u8; 32] = [
    0xa1, 0xb2, 0xc3, 0xd4, 0xe5, 0xf6, 0x07, 0x18, 0x29, 0x3a, 0x4b, 0x5c, 0x6d, 0x7e, 0x8f, 0x90,
    0x01, 0x12, 0x23, 0x34, 0x45, 0x56, 0x67, 0x78, 0x89, 0x9a, 0xab, 0xbc, 0xcd, 0xde, 0xef, 0xf0,
];

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
    let log = std::env::temp_dir().join(format!("ashs_{tag}_{pid}_{n}.log"));
    (Cleanup::new(&[&log]), log)
}

#[test]
fn handshake_publish_subscribe_and_resume() {
    let (_tmp, log) = log_path("ok");
    let _ = std::fs::remove_file(&log);

    let broker = Broker::open(&log).unwrap();
    let h = broker.serve_tcp_handshake("127.0.0.1:0", PSK).unwrap();
    let addr = h.tcp_addr().expect("a TCP endpoint").to_string();

    // Publish over a fresh forward-secret session.
    let mut p = Client::connect_tcp_handshake(&addr, PSK).unwrap();
    for i in 1..=4u64 {
        let (off, dup) = p
            .publish(1, i, "/a/stream/x", format!("m{i}").as_bytes())
            .unwrap();
        assert_eq!((off, dup), (i - 1, false));
    }

    // Subscribe over ANOTHER forward-secret session (a different ephemeral key,
    // hence a different session key) and get ordered exactly-once delivery.
    let mut sub = Client::connect_tcp_handshake(&addr, PSK)
        .unwrap()
        .subscribe(0, "/a/stream/>")
        .unwrap();
    let got: Vec<(u64, String, Vec<u8>)> = (0..4).map(|_| sub.recv().unwrap().unwrap()).collect();
    assert_eq!(got[0], (0, "/a/stream/x".to_string(), b"m1".to_vec()));
    assert_eq!(got[3].0, 3);

    // Resume from offset 2 over yet another session: gapless, no dup.
    drop(sub);
    let mut sub2 = Client::connect_tcp_handshake(&addr, PSK)
        .unwrap()
        .subscribe(2, "/a/stream/>")
        .unwrap();
    assert_eq!(
        sub2.recv().unwrap().unwrap(),
        (2, "/a/stream/x".to_string(), b"m3".to_vec())
    );

    // Exactly-once ingest holds over the handshaken wire too.
    assert_eq!(p.publish(1, 2, "/a/stream/x", b"m2").unwrap(), (1, true));
}

#[test]
fn wrong_psk_is_refused() {
    let (_tmp, log) = log_path("wrongpsk");
    let _ = std::fs::remove_file(&log);
    let broker = Broker::open(&log).unwrap();
    let h = broker.serve_tcp_handshake("127.0.0.1:0", PSK).unwrap();
    let addr = h.tcp_addr().expect("a TCP endpoint").to_string();

    let mut wrong = PSK;
    wrong[0] ^= 0xff;

    // The DH completes, but the derived session keys differ, so the first sealed
    // frame fails to open and the connection is dropped. Deadline-guarded.
    let (tx, rx) = mpsc::channel();
    let addr2 = addr.clone();
    std::thread::spawn(move || {
        let res = (|| {
            let mut c = Client::connect_tcp_handshake(&addr2, wrong)?;
            c.publish(1, 1, "/a/stream/x", b"intruder")
        })();
        let _ = tx.send(res.is_err());
    });
    match rx.recv_timeout(Duration::from_secs(5)) {
        Ok(errored) => assert!(
            errored,
            "a wrong-PSK handshake must not establish a session"
        ),
        Err(_) => panic!("wrong-PSK publish neither completed nor was refused within 5s"),
    }

    // A correctly-keyed client still works afterward.
    let mut good = Client::connect_tcp_handshake(&addr, PSK).unwrap();
    assert_eq!(
        good.publish(1, 1, "/a/stream/x", b"legit").unwrap(),
        (0, false)
    );
}

#[test]
fn plaintext_peer_is_refused() {
    // A client that skips the handshake (plain connect_tcp) sends a Frame where the
    // server expects the handshake's magic — bad magic, connection dropped. Proves
    // the handshake is mandatory, not optional, on a handshake endpoint.
    let (_tmp, log) = log_path("plain");
    let _ = std::fs::remove_file(&log);
    let broker = Broker::open(&log).unwrap();
    let h = broker.serve_tcp_handshake("127.0.0.1:0", PSK).unwrap();
    let addr = h.tcp_addr().expect("a TCP endpoint").to_string();

    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let res = (|| {
            let mut c = Client::connect_tcp(&addr)?;
            c.publish(1, 1, "/a/stream/x", b"cleartext")
        })();
        let _ = tx.send(res.is_err());
    });
    match rx.recv_timeout(Duration::from_secs(5)) {
        Ok(errored) => assert!(
            errored,
            "a plaintext peer must be refused on a handshake endpoint"
        ),
        Err(_) => panic!("plaintext publish neither completed nor was refused within 5s"),
    }
}

#[test]
fn a_silent_peer_does_not_block_others() {
    // Slowloris mitigation: a peer that TCP-connects then never sends its handshake
    // message parks only its own connection thread (bounded by HANDSHAKE_TIMEOUT) —
    // the acceptor and other connections stay live. We keep the silent socket open
    // for the whole test; a normal client must still handshake + publish promptly.
    let (_tmp, log) = log_path("silent");
    let _ = std::fs::remove_file(&log);
    let broker = Broker::open(&log).unwrap();
    let h = broker.serve_tcp_handshake("127.0.0.1:0", PSK).unwrap();
    let addr = h.tcp_addr().expect("a TCP endpoint").to_string();

    // A raw socket that connects and says nothing — its server-side handshake stalls.
    let _silent = std::net::TcpStream::connect(&addr).unwrap();

    let (tx, rx) = mpsc::channel();
    let addr2 = addr.clone();
    std::thread::spawn(move || {
        let res = (|| {
            let mut c = Client::connect_tcp_handshake(&addr2, PSK)?;
            c.publish(1, 1, "/a/stream/x", b"alive")
        })();
        let _ = tx.send(res);
    });
    match rx.recv_timeout(Duration::from_secs(5)) {
        Ok(res) => assert_eq!(
            res.unwrap(),
            (0, false),
            "a normal client must work while a silent peer is parked"
        ),
        Err(_) => panic!("a silent peer blocked a normal client — slowloris not mitigated"),
    }
    drop(_silent);
}
