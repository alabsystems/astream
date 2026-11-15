//! Client-side protocol regressions: a `Client` must stay IN STEP with the broker —
//! every request's response read by that request — or the next call reads a response
//! that belongs to an earlier one and reports it as its own.
#![cfg(unix)]

use astream_broker::proto::{
    decode_request, encode_response, read_frame, write_frame, Response, ERR_RECORD_REFUSED,
    PROTO_VERSION,
};
use astream_broker::{broker_refusal, Broker, BrokerHandle, Client};
use astream_wire::{Frame, MAX_PAYLOAD_LEN};
use std::collections::VecDeque;
use std::io::{self, Read, Write};
use std::os::unix::net::UnixListener;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};

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
    assert!(
        broker_refusal(&err).is_some_and(|r| r.code == ERR_RECORD_REFUSED && r.is_permanent()),
        "a record too large for the log can never land: {err:?}"
    );

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
            durable: None,
            oldest: None,
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

/// One side of an in-memory connection: reads play `replies` in order (a chunk of
/// bytes, or an error), then EOF; writes land in `written`, unless `fail_write` is
/// set, which fails the next one.
struct Wire {
    replies: VecDeque<io::Result<Vec<u8>>>,
    written: Arc<Mutex<Vec<u8>>>,
    fail_write: bool,
}

impl Read for Wire {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        match self.replies.pop_front() {
            None => Ok(0),
            Some(Err(e)) => Err(e),
            Some(Ok(mut chunk)) => {
                let n = chunk.len().min(buf.len());
                buf[..n].copy_from_slice(&chunk[..n]);
                if n < chunk.len() {
                    self.replies.push_front(Ok(chunk.split_off(n)));
                }
                Ok(n)
            }
        }
    }
}

impl Write for Wire {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        if std::mem::take(&mut self.fail_write) {
            return Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "scripted write timeout",
            ));
        }
        self.written.lock().unwrap().extend_from_slice(buf);
        Ok(buf.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// What a [`Wire`] answers, read by read.
type Script = Vec<io::Result<Vec<u8>>>;

fn reply(r: &Response) -> io::Result<Vec<u8>> {
    Ok(Frame::new(encode_response(r)).encode().unwrap())
}

fn mark(next: u64) -> Response {
    Response::Mark {
        next,
        head: next,
        resume: String::new(),
        durable: None,
        oldest: None,
    }
}

/// A request that fails PART-WAY THROUGH ITS EXCHANGE leaves the connection at an
/// unknown point — its reply may still arrive, late — so the client latches out of
/// step: the next request fails at once with `BrokenPipe` (never `Other`, which is a
/// broker refusal), writes nothing, and never reads the late reply as its own. Each
/// failure an exchange can meet: a read that times out (with the late reply queued
/// behind it), EOF, a reply that does not decode, a reply of the wrong kind, a page
/// longer than it asked for, a write that fails.
#[test]
fn a_request_that_fails_mid_exchange_refuses_the_next_one() {
    let late = || reply(&mark(9));
    let delivery = || {
        reply(&Response::Delivery {
            offset: 7,
            subject: "/a/x".into(),
            body: vec![],
        })
    };
    let cases: Vec<(&str, Script, bool, io::ErrorKind)> = vec![
        (
            "read timeout",
            vec![
                Err(io::Error::new(io::ErrorKind::TimedOut, "scripted")),
                late(),
            ],
            false,
            io::ErrorKind::TimedOut,
        ),
        ("eof", vec![], false, io::ErrorKind::UnexpectedEof),
        // In THIS protocol: a reply stamped with another version byte is a protocol
        // mismatch (tests/suite/protocol_mismatch.rs), which latches the same way.
        (
            "undecodable reply",
            vec![
                Ok(Frame::new(vec![PROTO_VERSION, 0xff]).encode().unwrap()),
                late(),
            ],
            false,
            io::ErrorKind::InvalidData,
        ),
        (
            "wrong reply",
            vec![
                reply(&Response::PublishAck {
                    offset: 3,
                    deduped: false,
                }),
                late(),
            ],
            false,
            io::ErrorKind::InvalidData,
        ),
        (
            "over-long page",
            vec![delivery(), delivery(), late()],
            false,
            io::ErrorKind::InvalidData,
        ),
        ("write failure", vec![late()], true, io::ErrorKind::TimedOut),
    ];
    for (what, replies, fail_write, kind) in cases {
        let written = Arc::new(Mutex::new(Vec::new()));
        let mut c = Client::from_stream(Wire {
            replies: replies.into(),
            written: written.clone(),
            fail_write,
        });
        let first = c.fetch(0, "/a/>", 1).expect_err(what);
        assert_eq!(first.kind(), kind, "{what}: {first}");
        let sent = written.lock().unwrap().len();
        let next = c
            .fetch(0, "/a/>", 1)
            .expect_err("the next request must not read the earlier one's reply");
        assert_eq!(next.kind(), io::ErrorKind::BrokenPipe, "{what}: {next}");
        assert!(broker_refusal(&next).is_none(), "{what}: not a refusal");
        assert_eq!(
            written.lock().unwrap().len(),
            sent,
            "{what}: nothing more was sent"
        );
    }
}

/// The negative control: a broker REFUSAL is a whole reply, so the client stays in
/// step — the refusal comes back typed, and the next request reads its own answer.
#[test]
fn a_refused_request_leaves_the_next_one_in_step() {
    let mut c = Client::from_stream(Wire {
        replies: vec![
            reply(&Response::Error {
                code: ERR_RECORD_REFUSED,
                msg: "message too large".into(),
            }),
            reply(&mark(4)),
        ]
        .into(),
        written: Arc::new(Mutex::new(Vec::new())),
        fail_write: false,
    });
    let e = c.fetch(0, "/a/>", 1).unwrap_err();
    assert_eq!(e.kind(), io::ErrorKind::Other);
    assert_eq!(
        e.to_string(),
        "message too large",
        "Display is the broker's words"
    );
    let r = broker_refusal(&e).expect("typed");
    assert_eq!((r.code, r.is_permanent()), (ERR_RECORD_REFUSED, true));
    assert_eq!(c.fetch(0, "/a/>", 1).unwrap(), (vec![], (4, 4)));
}
