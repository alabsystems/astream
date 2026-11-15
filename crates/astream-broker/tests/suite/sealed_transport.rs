//! Evidence for `broker.sealed-tcp-roundtrip`: the SAME exactly-once pub/sub +
//! resume works over an XChaCha20-Poly1305-SEALED TCP transport — confidential and
//! authenticated across an untrusted network — a peer without the pre-shared key
//! is refused inside the handshake, and unauthenticated peers are bounded on the
//! accept path. This is Rung 6 of the drive pipe: the AEAD wire the capability
//! mint's authorization half does not cover.
#![cfg(feature = "aead")]

use astream_aead::{HELLO_LEN, HELLO_MAGIC, OVERHEAD};
use astream_broker::MAX_RECORD_PAYLOAD;
use astream_broker::{Broker, BrokerHandle, Client};
use std::io::{ErrorKind, Read, Write};
use std::net::TcpStream;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

static CTR: AtomicU64 = AtomicU64::new(0);

const KEY: [u8; 32] = [
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff, 0x00,
    0x0f, 0x1e, 0x2d, 0x3c, 0x4b, 0x5a, 0x69, 0x78, 0x87, 0x96, 0xa5, 0xb4, 0xc3, 0xd2, 0xe1, 0xf0,
];

/// Removes its paths when dropped, each with every `<path>.*` sidecar beside it (the
/// broker's `.hw`, `.base`, `.replica`, …), so a test leaves nothing behind whether it
/// passes or panics. Bind it before whatever uses the paths, so it drops after that.
struct Cleanup(Vec<PathBuf>);

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

/// A fresh broker on a fresh log, serving the sealed transport on an ephemeral
/// port. Returns the guard that removes the log, the broker (kept alive), its
/// handle, and the address.
fn sealed_broker(tag: &str) -> (Cleanup, Broker, BrokerHandle, String) {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = std::env::temp_dir().join(format!("assealed_{tag}_{pid}_{n}.log"));
    let _ = std::fs::remove_file(&log);
    let tmp = Cleanup::new(&[&log]);
    let broker = Broker::open(&log).unwrap();
    let h = broker.serve_tcp_sealed("127.0.0.1:0", KEY).unwrap();
    let addr = h.tcp_addr().expect("a TCP endpoint").to_string();
    (tmp, broker, h, addr)
}

#[test]
fn sealed_publish_subscribe_and_resume() {
    let (_tmp, _b, _h, addr) = sealed_broker("rt");

    // Publish over the sealed transport.
    let mut p = Client::connect_tcp_sealed(&addr, KEY).unwrap();
    for i in 1..=4u64 {
        let (off, dup) = p
            .publish(1, i, "/a/stream/x", format!("m{i}").as_bytes())
            .unwrap();
        assert_eq!((off, dup), (i - 1, false));
    }

    // Subscribe over the sealed transport from 0: ordered exactly-once delivery,
    // the plaintext of every frame reconstructed from the encrypted record stream.
    let mut sub = Client::connect_tcp_sealed(&addr, KEY)
        .unwrap()
        .subscribe(0, "/a/stream/>")
        .unwrap();
    let got: Vec<(u64, String, Vec<u8>)> = (0..4).map(|_| sub.recv().unwrap().unwrap()).collect();
    assert_eq!(got[0], (0, "/a/stream/x".to_string(), b"m1".to_vec()));
    assert_eq!(got[3].0, 3);

    // Resume from offset 2 after a disconnect: gapless, no dup.
    drop(sub);
    let mut sub2 = Client::connect_tcp_sealed(&addr, KEY)
        .unwrap()
        .subscribe(2, "/a/stream/>")
        .unwrap();
    assert_eq!(
        sub2.recv().unwrap().unwrap(),
        (2, "/a/stream/x".to_string(), b"m3".to_vec())
    );
    assert_eq!(sub2.recv().unwrap().unwrap().0, 3);

    // Exactly-once ingest holds over the sealed wire too: a re-send dedups.
    assert_eq!(p.publish(1, 2, "/a/stream/x", b"m2").unwrap(), (1, true));
}

#[test]
fn one_connection_publishes_then_subscribes_over_shared_counters() {
    // The acks for a publish are written by the broker's ack-writer CLONE of the
    // sealed stream; a later subscribe's deliveries are written by the main
    // handle. Doing both on ONE connection means the client's single receive
    // counter must line up with records from BOTH broker-side handles — which it
    // does only if `try_clone` shares the counters. (A clone with fresh counters
    // would seal its first ack under a sequence the client has already consumed,
    // and the publish — or, with the clone made later, the first delivery — would
    // fail to authenticate.)
    let (_tmp, _b, _h, addr) = sealed_broker("shared");
    let mut c = Client::connect_tcp_sealed(&addr, KEY).unwrap();
    assert_eq!(c.publish(1, 1, "/a/stream/x", b"m1").unwrap(), (0, false));
    assert_eq!(c.publish(1, 2, "/a/stream/x", b"m2").unwrap(), (1, false));
    let mut sub = c.subscribe(0, "/a/stream/>").unwrap();
    assert_eq!(
        sub.recv().unwrap().unwrap(),
        (0, "/a/stream/x".to_string(), b"m1".to_vec())
    );
    assert_eq!(
        sub.recv().unwrap().unwrap(),
        (1, "/a/stream/x".to_string(), b"m2".to_vec())
    );
}

#[test]
fn a_max_size_record_crosses_the_sealed_wire() {
    // The largest record the store accepts: a BrokerRecord frame of exactly
    // MAX_RECORD_PAYLOAD (MAX_PAYLOAD_LEN minus the 16 bytes a Replicate
    // envelope adds, so every stored record can also be shipped to a follower;
    // 34 fixed bytes + subject + body, no commit). Its Publish
    // request frame and its Delivery frame are both within a few bytes of 16 MiB,
    // so each is carried as many bounded sealed records and reassembled: the
    // publish is accepted and the delivery comes back byte-identical, and the
    // connection is intact afterwards. (Previously the sealed reader's record
    // ceiling equalled the frame payload cap, so a near-max record was durably
    // stored yet could never cross the sealed wire — wedging every sealed
    // subscriber behind it.)
    let (_tmp, _b, _h, addr) = sealed_broker("max");
    let subject = "/a/stream/big";
    let body_len = MAX_RECORD_PAYLOAD - 34 - subject.len();
    let body: Vec<u8> = (0..body_len).map(|i| (i % 253) as u8).collect();

    let mut p = Client::connect_tcp_sealed(&addr, KEY).unwrap();
    assert_eq!(p.publish(1, 1, subject, &body).unwrap(), (0, false));
    // ...and it IS the largest the store accepts: one more body byte makes a
    // record over the cap, refused as too large (the request frame itself still
    // fits, so the refusal is the store's, carried back over the sealed wire).
    let mut over = body.clone();
    over.push(0xff);
    let e = p.publish(1, 2, subject, &over).unwrap_err();
    assert!(
        e.to_string().contains("too large"),
        "one byte over the cap: {e}"
    );

    let mut sub = Client::connect_tcp_sealed(&addr, KEY)
        .unwrap()
        .subscribe(0, "/a/stream/>")
        .unwrap();
    let (off, subj, got) = sub.recv().unwrap().unwrap();
    assert_eq!((off, subj.as_str()), (0, subject));
    assert_eq!(got.len(), body_len);
    assert!(got == body, "the max-size body must arrive byte-identical");

    // The streams are intact after the giant frames: a small record still flows.
    assert_eq!(p.publish(1, 3, subject, b"after").unwrap(), (1, false));
    assert_eq!(sub.recv().unwrap().unwrap().2, b"after");
}

/// Read one byte with the socket's timeout; `true` iff the peer closed.
fn closed(raw: &mut TcpStream) -> bool {
    let mut b = [0u8; 1];
    match raw.read(&mut b) {
        Ok(0) => true,
        Ok(_) => false,
        Err(e) => e.kind() == ErrorKind::ConnectionReset,
    }
}

#[test]
fn a_peer_without_the_key_is_refused_inside_the_handshake() {
    let (_tmp, _b, _h, addr) = sealed_broker("wk");

    // (1) The client library under the WRONG key: the connect itself fails — the
    //     broker's confirm does not open under the wrong key — so no request is
    //     ever sent, and the broker (whose open of OUR confirm failed too) has
    //     dropped the connection.
    let mut wrong = KEY;
    wrong[0] ^= 0xff;
    let e = Client::connect_tcp_sealed(&addr, wrong)
        .err()
        .expect("a wrong-key connect must fail");
    assert_eq!(e.kind(), ErrorKind::InvalidData, "{e}");

    // (2) A raw peer with NO key, speaking the handshake by hand: a well-formed
    //     hello, then a forged confirm (the right length, arbitrary bytes). The
    //     broker sends exactly its own hello and confirm — HELLO_LEN + 4 + OVERHEAD
    //     bytes, both emitted before it can know the peer is unkeyed — and then
    //     CLOSES: not one application byte is written to an unauthenticated peer.
    //     A broker that skipped authentication would instead sit waiting for a
    //     frame (a read timeout here) or answer the forged record.
    let mut raw = TcpStream::connect(&addr).unwrap();
    raw.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
    let mut hello = [0x42u8; HELLO_LEN];
    hello[..HELLO_MAGIC.len()].copy_from_slice(&HELLO_MAGIC);
    raw.write_all(&hello).unwrap();
    let mut theirs = [0u8; HELLO_LEN];
    raw.read_exact(&mut theirs).unwrap();
    assert_eq!(&theirs[..HELLO_MAGIC.len()], &HELLO_MAGIC);
    let mut forged = vec![0u8; 4 + OVERHEAD];
    forged[..4].copy_from_slice(&(OVERHEAD as u32).to_le_bytes());
    for (i, b) in forged[4..].iter_mut().enumerate() {
        *b = (i * 7 + 3) as u8;
    }
    raw.write_all(&forged).unwrap();
    let mut confirm = vec![0u8; 4 + OVERHEAD];
    raw.read_exact(&mut confirm).unwrap();
    let declared = u32::from_le_bytes([confirm[0], confirm[1], confirm[2], confirm[3]]) as usize;
    assert_eq!(
        declared, OVERHEAD,
        "the broker's confirm is an empty record"
    );
    assert!(
        closed(&mut raw),
        "the broker must close without writing anything after its confirm"
    );

    // The broker is unharmed: a correctly-keyed client still works.
    let mut good = Client::connect_tcp_sealed(&addr, KEY).unwrap();
    assert_eq!(
        good.publish(1, 1, "/a/stream/x", b"legit").unwrap(),
        (0, false)
    );
}

#[test]
fn a_stalled_unauthenticated_peer_is_dropped_at_the_deadline() {
    // A peer that connects and then sends nothing holds a broker thread only
    // until the pre-authentication deadline (5 s), after which the broker closes
    // it: an unkeyed peer cannot park a thread (or a socket) indefinitely.
    let (_tmp, _b, _h, addr) = sealed_broker("stall");
    let mut raw = TcpStream::connect(&addr).unwrap();
    raw.set_read_timeout(Some(Duration::from_secs(15))).unwrap();
    let t0 = Instant::now();
    let mut hello = [0u8; HELLO_LEN];
    raw.read_exact(&mut hello).unwrap(); // the broker's hello arrives at once
    assert!(closed(&mut raw), "the stalled peer must be dropped");
    let waited = t0.elapsed();
    assert!(
        waited >= Duration::from_secs(4) && waited < Duration::from_secs(12),
        "dropped at the deadline, not before it and not never: {waited:?}"
    );
}

#[test]
fn unauthenticated_connections_are_capped() {
    // At most 64 connections may sit in the handshake at once. With 64 stalled
    // peers held, the next accept is dropped IMMEDIATELY (well before the 5 s
    // deadline) instead of being given a thread, while the held ones stay open
    // until their deadline.
    const CAP: usize = 64;
    let (_tmp, _b, _h, addr) = sealed_broker("cap");
    let held: Vec<TcpStream> = (0..CAP)
        .map(|_| {
            let s = TcpStream::connect(&addr).unwrap();
            s.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
            s
        })
        .collect();
    // Each held connection has been taken into a handshake once the broker's
    // hello has arrived on it.
    for s in &held {
        let mut hello = [0u8; HELLO_LEN];
        (&*s).read_exact(&mut hello).unwrap();
        assert_eq!(&hello[..HELLO_MAGIC.len()], &HELLO_MAGIC);
    }
    let mut extra = TcpStream::connect(&addr).unwrap();
    extra
        .set_read_timeout(Some(Duration::from_secs(3)))
        .unwrap();
    let t0 = Instant::now();
    assert!(
        closed(&mut extra),
        "the connection beyond the cap must be dropped at once"
    );
    assert!(
        t0.elapsed() < Duration::from_secs(3),
        "dropped by the cap, not by the deadline"
    );
    // The held connections are still in their handshake: a short read on one
    // times out (still open) rather than seeing EOF.
    held[0]
        .set_read_timeout(Some(Duration::from_millis(200)))
        .unwrap();
    let mut b = [0u8; 1];
    let e = (&held[0]).read(&mut b).unwrap_err();
    assert!(
        matches!(e.kind(), ErrorKind::WouldBlock | ErrorKind::TimedOut),
        "a held connection is still open: {e}"
    );
    drop(held);
}
