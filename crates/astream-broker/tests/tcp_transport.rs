//! Evidence for `broker.tcp-transport`: the SAME exactly-once pub/sub + resume works
//! over TCP, not just a Unix socket — multi-machine. Plain `serve_tcp` is PLAINTEXT and
//! unauthenticated (a trusted network only); the sealed transport (`serve_tcp_sealed`,
//! the `aead` feature, claim `broker.sealed-tcp-roundtrip`) and capability enforcement
//! (`open_guarded`, the `cap` feature) are the built answers for an untrusted one. The
//! broker binds an ephemeral TCP port and a TCP client drives it with the identical
//! Frame protocol. Also witnessed here, transport-independently: the pre-first-frame
//! bound on an unknown peer and the connection cap, so an unauthenticated flood cannot
//! pin threads and frame buffers.

use astream_broker::proto::{decode_response, read_frame};
use astream_broker::{Broker, Client, Response};
use std::io::{Read, Write};
use std::net::TcpStream;
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

fn log_path(tag: &str) -> (Cleanup, std::path::PathBuf) {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    // temp_dir(), not a /tmp literal: these tests are TCP-only and run on Windows too.
    let log = std::env::temp_dir().join(format!("astcp_{tag}_{pid}_{n}.log"));
    let _ = std::fs::remove_file(&log);
    (Cleanup::new(&[&log]), log)
}

/// Whether the broker closed this socket: a read returns EOF (or a reset), never a
/// timeout (which would mean the connection is still parked open).
fn closed_by_broker(s: &mut TcpStream) -> bool {
    let mut b = [0u8; 8];
    match s.read(&mut b) {
        Ok(0) => true,
        Ok(_) => false,
        Err(e) => !matches!(
            e.kind(),
            std::io::ErrorKind::WouldBlock | std::io::ErrorKind::TimedOut
        ),
    }
}

#[test]
fn tcp_publish_subscribe_and_resume() {
    let (_tmp, log) = log_path("rt");

    let broker = Broker::open(&log).unwrap();
    let h = broker.serve_tcp("127.0.0.1:0").unwrap();
    let addr = h.tcp_addr().expect("a TCP endpoint").to_string();

    // Publish over TCP.
    let mut p = Client::connect_tcp(&addr).unwrap();
    for i in 1..=4u64 {
        let (off, dup) = p
            .publish(1, i, "/a/stream/x", format!("m{i}").as_bytes())
            .unwrap();
        assert_eq!((off, dup), (i - 1, false));
    }
    // Subscribe over TCP from 0: ordered exactly-once delivery.
    let mut sub = Client::connect_tcp(&addr)
        .unwrap()
        .subscribe(0, "/a/stream/>")
        .unwrap();
    let got: Vec<u64> = (0..4).map(|_| sub.recv().unwrap().unwrap().0).collect();
    assert_eq!(got, vec![0, 1, 2, 3]);

    // Resume over TCP from offset 2 after a disconnect: gapless, no dup.
    drop(sub);
    let mut sub2 = Client::connect_tcp(&addr)
        .unwrap()
        .subscribe(2, "/a/stream/>")
        .unwrap();
    assert_eq!(
        sub2.recv().unwrap().unwrap(),
        (2, "/a/stream/x".to_string(), b"m3".to_vec())
    );
    assert_eq!(sub2.recv().unwrap().unwrap().0, 3);

    // Exactly-once ingest holds over TCP too: a re-send dedups to the original offset.
    assert_eq!(p.publish(1, 2, "/a/stream/x", b"m2").unwrap(), (1, true));
}

/// Until a connection has sent its first complete frame nothing is known about the
/// peer, so that wait is BOUNDED: a socket that connects and idles, or trickles a
/// length prefix and stops, is closed after the first-frame timeout instead of pinning
/// a thread and a frame buffer for as long as it likes. An ESTABLISHED connection is
/// not on a timer — a quiet producer stays connected (shutdown's force-close reaps it).
#[test]
fn a_connection_that_never_sends_a_frame_is_reaped_after_the_first_frame_timeout() {
    let (_tmp, log) = log_path("ff");
    let broker = Broker::open(&log).unwrap();
    broker.set_first_frame_timeout(Duration::from_millis(200));
    let h = broker.serve_tcp("127.0.0.1:0").unwrap();
    let addr = h.tcp_addr().unwrap().to_string();

    // An established producer, connected and framed BEFORE the loiterers.
    let mut p = Client::connect_tcp(&addr).unwrap();
    assert_eq!(p.publish(1, 1, "/a/stream/x", b"m1").unwrap(), (0, false));
    // Two loiterers: one never sends, one sends 2 bytes of a length prefix and stops.
    let mut idle = TcpStream::connect(&addr).unwrap();
    idle.set_read_timeout(Some(Duration::from_secs(10)))
        .unwrap();
    let mut trickle = TcpStream::connect(&addr).unwrap();
    trickle.write_all(&[0, 0]).unwrap();
    trickle
        .set_read_timeout(Some(Duration::from_secs(10)))
        .unwrap();
    assert!(
        closed_by_broker(&mut idle),
        "the idle connection was not reaped"
    );
    assert!(
        closed_by_broker(&mut trickle),
        "the trickling connection was not reaped"
    );
    // By now more than the timeout has passed since the producer's first frame: it is
    // still connected and serving — the bound is on the first frame only.
    assert_eq!(p.publish(1, 2, "/a/stream/x", b"m2").unwrap(), (1, false));
}

/// Simultaneous connections are CAPPED: a connection beyond the cap is answered with an
/// error frame and closed, the connections within it are unaffected, and a closed
/// connection frees its slot.
#[test]
fn connections_beyond_the_cap_are_refused_and_the_rest_keep_serving() {
    let (_tmp, log) = log_path("cap");
    let broker = Broker::open(&log).unwrap();
    broker.set_max_conns(2);
    let h = broker.serve_tcp("127.0.0.1:0").unwrap();
    let addr = h.tcp_addr().unwrap().to_string();

    let mut c1 = Client::connect_tcp(&addr).unwrap();
    assert_eq!(c1.publish(1, 1, "/a/stream/x", b"m1").unwrap(), (0, false));
    let mut c2 = Client::connect_tcp(&addr).unwrap();
    assert_eq!(c2.publish(1, 2, "/a/stream/x", b"m2").unwrap(), (1, false));
    // The third is told why, then closed.
    let mut c3 = TcpStream::connect(&addr).unwrap();
    c3.set_read_timeout(Some(Duration::from_secs(10))).unwrap();
    let payload = read_frame(&mut c3)
        .unwrap()
        .expect("an error frame, not a silent drop");
    match decode_response(&payload) {
        Some(Response::Error { msg, .. }) => {
            assert!(msg.contains("too many connections"), "{msg}")
        }
        other => panic!("expected an error frame, got {other:?}"),
    }
    assert!(closed_by_broker(&mut c3));
    // Within the cap: unaffected.
    assert_eq!(c1.publish(1, 3, "/a/stream/x", b"m3").unwrap(), (2, false));
    // Closing one frees its slot once the broker has reaped it — a liveness property,
    // so probe with bounded retries rather than a fixed wait.
    drop(c2);
    let mut admitted = None;
    for _ in 0..400 {
        let mut c = Client::connect_tcp(&addr).unwrap();
        match c.publish(1, 4, "/a/stream/x", b"m4") {
            Ok(ack) => {
                admitted = Some(ack);
                break;
            }
            Err(_) => std::thread::sleep(Duration::from_millis(5)),
        }
    }
    assert_eq!(
        admitted,
        Some((3, false)),
        "the freed slot admits a new connection"
    );
}
