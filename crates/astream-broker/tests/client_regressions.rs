//! Client-side protocol regressions: a `Client` must stay IN STEP with the broker —
//! every request's response read by that request — or the next call reads a response
//! that belongs to an earlier one and reports it as its own.
#![cfg(unix)]

use astream_broker::proto::{decode_request, encode_response, read_frame, write_frame, Response};
use astream_broker::{Broker, BrokerHandle, Client};
use astream_wire::MAX_PAYLOAD_LEN;
use std::os::unix::net::UnixListener;
use std::sync::atomic::{AtomicU64, Ordering};

static CTR: AtomicU64 = AtomicU64::new(0);

struct Paths {
    sock: String,
    log: String,
}

impl Drop for Paths {
    /// Remove the socket, the log and every `<path>.*` sidecar beside them (the
    /// broker's `.hw`, `.base`, `.replica`, …) on success and on panic alike. A test
    /// binds its `Paths` before serving on them, so this runs after the broker is gone.
    fn drop(&mut self) {
        remove_with_sidecars(&self.sock);
        remove_with_sidecars(&self.log);
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

fn fresh(tag: &str) -> Paths {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let p = Paths {
        sock: format!("/tmp/asclient_{tag}_{pid}_{n}.sock"),
        log: format!("/tmp/asclient_{tag}_{pid}_{n}.log"),
    };
    let _ = std::fs::remove_file(&p.sock);
    let _ = std::fs::remove_file(&p.log);
    p
}

fn serve(p: &Paths) -> (Broker, BrokerHandle) {
    let broker = Broker::open(&p.log).unwrap();
    let handle = broker.serve(&p.sock).unwrap();
    (broker, handle)
}

/// Where the record whose body is `body` actually landed, read on a FRESH connection
/// so the answer cannot be skewed by the connection under test.
fn offset_of(sock: &str, filter: &str, body: &[u8]) -> u64 {
    let (page, _) = Client::connect(sock).unwrap().fetch(0, filter, 64).unwrap();
    page.iter()
        .find(|(_, _, b)| b == body)
        .unwrap_or_else(|| panic!("no record with body {body:?} in {page:?}"))
        .0
}

/// `publish_pipelined` gives up on the first publish it cannot complete, but by then
/// the publishes ahead of it in the window are already on the wire. Their acks must
/// be read off the connection before the error is returned: left there, the NEXT
/// blocking call reads the ack of an earlier pipelined publish and returns that
/// record's offset as its own.
///
/// Here the failure is client-side — a body too large to frame, refused before a byte
/// of it is written — so the connection itself is healthy and must stay usable.
#[test]
fn a_pipelined_publish_that_cannot_be_framed_leaves_the_connection_in_step() {
    let p = fresh("pipeframe");
    let (_b, _h) = serve(&p);
    let mut c = Client::connect(&p.sock).unwrap();

    let huge = vec![0u8; MAX_PAYLOAD_LEN + 1];
    let bodies: Vec<&[u8]> = vec![b"one", b"two", &huge, b"four"];
    let err = c
        .publish_pipelined(7, "/a/pipe/x", &bodies, 8)
        .expect_err("the unframeable body fails the pipeline");
    assert_eq!(err.kind(), std::io::ErrorKind::InvalidData, "{err}");

    let (off, dup) = c.publish(8, 1, "/a/pipe/after", b"after").unwrap();
    assert!(!dup);
    assert_eq!(
        off,
        offset_of(&p.sock, "/a/pipe/>", b"after"),
        "publish returned an offset that is not its own record's"
    );
    // And a bounded read on the same connection sees a page, not a stray ack.
    let (page, _) = c.fetch(0, "/a/pipe/>", 64).unwrap();
    assert_eq!(page.len(), 3, "one, two, after: {page:?}");
}

/// The same, when the BROKER refuses one publish in the window: its `Error` arrives
/// in ack order and the acks of the publishes behind it follow. The body is sized to
/// fit a request frame but not a durable record (the record's envelope is larger than
/// the request's), so the refusal comes from the broker, after the frames behind it
/// were already sent.
#[test]
fn a_pipelined_publish_the_broker_refuses_leaves_the_connection_in_step() {
    let p = fresh("piperefuse");
    let (_b, _h) = serve(&p);
    let mut c = Client::connect(&p.sock).unwrap();

    let subject = "/a/pipe/x";
    // A Publish payload is 26 bytes + subject + body; a record's is 34 + subject + body
    // against a cap 16 bytes under the frame's.
    let refused = vec![0u8; MAX_PAYLOAD_LEN - 26 - subject.len()];
    let bodies: Vec<&[u8]> = vec![b"one", &refused, b"three", b"four"];
    let err = c
        .publish_pipelined(7, subject, &bodies, 8)
        .expect_err("the broker refuses the oversized record");
    assert_eq!(err.kind(), std::io::ErrorKind::Other, "{err}");

    let (off, dup) = c.publish(8, 1, "/a/pipe/after", b"after").unwrap();
    assert!(!dup);
    assert_eq!(
        off,
        offset_of(&p.sock, "/a/pipe/>", b"after"),
        "publish returned an offset that is not its own record's"
    );
}

/// A fake broker that answers ONE request with `rows` deliveries and a closing `Mark`.
fn fake_page_broker(sock: &str, rows: u64) -> std::thread::JoinHandle<()> {
    let listener = UnixListener::bind(sock).unwrap();
    std::thread::spawn(move || {
        let (mut s, _) = listener.accept().unwrap();
        let req = read_frame(&mut s).unwrap().unwrap();
        decode_request(&req).expect("a well-formed request");
        for offset in 0..rows {
            let d = Response::Delivery {
                offset,
                subject: "/a/x".into(),
                body: vec![],
            };
            if write_frame(&mut s, &encode_response(&d)).is_err() {
                return; // the client hung up on a page it refused
            }
        }
        let mark = Response::Mark {
            next: rows,
            head: rows,
            resume: String::new(),
        };
        let _ = write_frame(&mut s, &encode_response(&mark));
    })
}

/// A bounded read BUFFERS its page before returning it, so the page must be bounded
/// by what the caller asked for — not by however many deliveries the peer chooses to
/// send before its `Mark`. A peer that keeps sending would otherwise grow the page
/// without limit.
#[test]
fn a_page_longer_than_max_is_refused_not_buffered() {
    let p = fresh("pagebound");
    let fake = fake_page_broker(&p.sock, 5);
    let mut c = Client::connect(&p.sock).unwrap();
    let err = c
        .fetch(0, "/a/>", 2)
        .expect_err("a page of 5 rows answers a request for at most 2");
    assert_eq!(err.kind(), std::io::ErrorKind::InvalidData, "{err}");
    drop(c);
    fake.join().unwrap();

    let p = fresh("pagebound_last");
    let fake = fake_page_broker(&p.sock, 3);
    let mut c = Client::connect(&p.sock).unwrap();
    let err = c
        .last_page("/a/>", "", 1)
        .expect_err("a page of 3 rows answers a request for at most 1");
    assert_eq!(err.kind(), std::io::ErrorKind::InvalidData, "{err}");
    drop(c);
    fake.join().unwrap();

    // A page within the bound is still read whole.
    let p = fresh("pagebound_ok");
    let fake = fake_page_broker(&p.sock, 2);
    let mut c = Client::connect(&p.sock).unwrap();
    let (page, (next, head)) = c.fetch(0, "/a/>", 2).unwrap();
    assert_eq!((page.len(), next, head), (2, 2, 2));
    fake.join().unwrap();
}
