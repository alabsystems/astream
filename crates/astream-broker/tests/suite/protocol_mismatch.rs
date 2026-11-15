//! Two ends that speak different astream protocols are TOLD so, on both sides.
//!
//! The broker answers a request whose version byte is not its own with one refusal in
//! the layout every protocol version keeps, stamped with the PEER's version byte so the
//! peer's decoder can read it, and then closes the connection. The client reads a reply
//! stamped with another version — all a broker that predates that refusal can send —
//! or the refusal itself as a `ProtocolMismatch` naming both versions, never as the
//! garbled stream ("unexpected response") it used to be indistinguishable from.

#![cfg(unix)]

use astream_broker::proto::{
    decode_response, encode_protocol_refusal, encode_request, encode_response, read_frame,
    write_frame, ERR_PROTOCOL, ERR_REFUSED, PROTO_VERSION,
};
use astream_broker::{
    broker_refusal, protocol_mismatch, Broker, Client, ProtocolMismatch, Request, Response,
};
use std::io::{self, Write};
use std::net::TcpStream;
use std::os::unix::net::UnixStream;
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;
use std::time::Duration;

static CTR: AtomicU64 = AtomicU64::new(0);

/// A wait for something that must happen: a hang detector, never a latency budget.
const HANG: Duration = Duration::from_secs(60);

/// Removes its paths when dropped, with every `<path>.*` sidecar beside them.
struct Cleanup(Vec<String>);

impl Drop for Cleanup {
    fn drop(&mut self) {
        for path in &self.0 {
            let path = std::path::Path::new(path);
            let _ = std::fs::remove_file(path);
            let (Some(dir), Some(name)) = (path.parent(), path.file_name()) else {
                continue;
            };
            let prefix = format!("{}.", name.to_string_lossy());
            for entry in std::fs::read_dir(dir).into_iter().flatten().flatten() {
                if entry.file_name().to_string_lossy().starts_with(&prefix) {
                    let _ = std::fs::remove_file(entry.path());
                }
            }
        }
    }
}

fn paths() -> (Cleanup, String, String) {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = format!("/tmp/asproto_{pid}_{n}.log");
    let sock = format!("/tmp/asproto_{pid}_{n}.sock");
    let _ = std::fs::remove_file(&log);
    (Cleanup(vec![log.clone(), sock.clone()]), log, sock)
}

/// `req`'s payload as a peer of protocol `version` would write it.
fn in_version(req: &Request, version: u8) -> Vec<u8> {
    let mut p = encode_request(req);
    p[0] = version;
    p
}

/// What the broker sends a raw connection that writes `frames` before reading: every
/// frame it answers with, up to its close.
fn answers<S: io::Read + Write>(mut s: S, frames: &[Vec<u8>]) -> Vec<Vec<u8>> {
    for f in frames {
        write_frame(&mut s, f).unwrap();
    }
    let mut got = Vec::new();
    while let Some(p) = read_frame(&mut s).unwrap() {
        got.push(p);
    }
    got
}

/// Over a Unix socket and TCP, a request in a protocol older or newer than the
/// broker's — the first frame, or one pipelined ahead of more — is answered with
/// exactly one protocol refusal stamped with the peer's version, and the broker
/// closes. The control: a frame in the broker's own protocol that it cannot decode
/// is the in-protocol "malformed request", and the connection stays usable.
#[test]
fn a_request_in_another_protocol_is_refused_in_the_peers_and_closed() {
    let (_tmp, log, sock) = paths();
    let b = Broker::open(&log).unwrap();
    let _uds = b.serve(&sock).unwrap();
    let tcp = b.serve_tcp("127.0.0.1:0").unwrap();
    let addr = tcp.tcp_addr().unwrap().to_string();
    for peer in [PROTO_VERSION - 1, PROTO_VERSION + 1] {
        let hello = in_version(&Request::Hello, peer);
        let fetch = in_version(
            &Request::Fetch {
                from_offset: 0,
                filter: "/a/>".into(),
                max: 1,
            },
            peer,
        );
        for frames in [vec![hello.clone()], vec![hello.clone(), fetch.clone()]] {
            let unix = UnixStream::connect(&sock).unwrap();
            unix.set_read_timeout(Some(HANG)).unwrap();
            let tcp = TcpStream::connect(&addr).unwrap();
            tcp.set_read_timeout(Some(HANG)).unwrap();
            for (wire, got) in [
                ("unix", answers(unix, &frames)),
                ("tcp", answers(tcp, &frames)),
            ] {
                assert_eq!(
                    got,
                    [encode_protocol_refusal(peer)],
                    "{wire}, peer protocol {peer}, {} frame(s)",
                    frames.len()
                );
            }
        }
    }

    let mut s = UnixStream::connect(&sock).unwrap();
    s.set_read_timeout(Some(HANG)).unwrap();
    write_frame(&mut s, &[PROTO_VERSION, 0xFF]).unwrap();
    let reply = read_frame(&mut s).unwrap().expect("a refusal");
    assert!(
        matches!(
            decode_response(&reply),
            Some(Response::Error {
                code: ERR_REFUSED,
                ..
            })
        ),
        "{reply:?}"
    );
    write_frame(&mut s, &encode_request(&Request::Hello)).unwrap();
    let reply = read_frame(&mut s).unwrap().expect("a nonce");
    assert!(
        matches!(decode_response(&reply), Some(Response::Nonce { .. })),
        "{reply:?}"
    );
}

/// On a guarded broker too, before anything is attached: a first frame in another
/// protocol is told so, not left to the pre-authentication deadline.
#[cfg(feature = "cap")]
#[test]
fn a_guarded_broker_refuses_another_protocol_before_any_attach() {
    let (_tmp, log, sock) = paths();
    let b = Broker::open_guarded(&log, b"proto-mismatch-guarded".to_vec()).unwrap();
    let _uds = b.serve(&sock).unwrap();
    let s = UnixStream::connect(&sock).unwrap();
    s.set_read_timeout(Some(HANG)).unwrap();
    let peer = PROTO_VERSION + 1;
    assert_eq!(
        answers(s, &[in_version(&Request::Hello, peer)]),
        [encode_protocol_refusal(peer)]
    );
}

/// A scripted broker on the other end of `ours`: it answers each request frame it
/// reads with the next of `replies`, then hands back the request frames it read
/// (including any it got after its replies ran out) once `ours` closes.
fn scripted(replies: Vec<Vec<u8>>) -> (UnixStream, thread::JoinHandle<Vec<Vec<u8>>>) {
    let (ours, mut theirs) = UnixStream::pair().unwrap();
    ours.set_read_timeout(Some(HANG)).unwrap();
    theirs.set_read_timeout(Some(HANG)).unwrap();
    let peer = thread::spawn(move || {
        let mut replies = replies.into_iter();
        let mut read = Vec::new();
        while let Ok(Some(p)) = read_frame(&mut theirs) {
            read.push(p);
            if let Some(reply) = replies.next() {
                write_frame(&mut theirs, &reply).unwrap();
            }
        }
        read
    });
    (ours, peer)
}

fn expect_mismatch(e: &io::Error, broker: u8, what: &str) {
    assert_eq!(
        protocol_mismatch(e),
        Some(&ProtocolMismatch {
            broker,
            client: PROTO_VERSION
        }),
        "{what}: {e:?}"
    );
    assert_eq!(e.kind(), io::ErrorKind::Unsupported, "{what}");
    assert!(broker_refusal(e).is_none(), "{what}: not a refusal");
}

/// The client names the mismatch whichever way the broker says it: a reply stamped
/// with its own other version (an older broker's "malformed request" — and an older
/// or newer broker's anything), or the protocol refusal stamped with ours that names
/// its version. Either way the connection is out of step: the next request fails
/// `BrokenPipe` and is not sent. The control is the same refusal in this protocol
/// with an ordinary code, which is a refusal and leaves the client in step.
#[test]
fn the_client_reads_a_broker_in_another_protocol_as_a_mismatch() {
    let malformed = Response::Error {
        code: ERR_REFUSED,
        msg: "malformed request".into(),
    };
    let stamped = |version: u8| {
        let mut p = encode_response(&malformed);
        p[0] = version;
        p
    };
    let refusal_naming = |broker: u8| {
        let mut p = encode_response(&Response::Error {
            code: ERR_PROTOCOL,
            msg: "this broker speaks another protocol".into(),
        });
        p.push(broker);
        p
    };
    for (what, reply, broker) in [
        (
            "an older broker",
            stamped(PROTO_VERSION - 1),
            PROTO_VERSION - 1,
        ),
        (
            "a newer broker",
            stamped(PROTO_VERSION + 1),
            PROTO_VERSION + 1,
        ),
        (
            "a refusal naming the broker's",
            refusal_naming(PROTO_VERSION + 1),
            PROTO_VERSION + 1,
        ),
    ] {
        let (ours, peer) = scripted(vec![reply]);
        let mut c = Client::from_stream(ours);
        expect_mismatch(&c.hello().unwrap_err(), broker, what);
        let again = c.hello().unwrap_err();
        assert_eq!(again.kind(), io::ErrorKind::BrokenPipe, "{what}: {again:?}");
        drop(c);
        assert_eq!(
            peer.join().unwrap().len(),
            1,
            "{what}: nothing more was sent"
        );
    }

    // The control: an ordinary refusal in this protocol keeps the client in step.
    let nonce = encode_response(&Response::Nonce {
        nonce: vec![7; 32],
        log: None,
        ext: astream_broker::NonceExt::default(),
    });
    let (ours, peer) = scripted(vec![encode_response(&malformed), nonce]);
    let mut c = Client::from_stream(ours);
    let refused = c.hello().unwrap_err();
    assert_eq!(broker_refusal(&refused).map(|r| r.code), Some(ERR_REFUSED));
    assert!(protocol_mismatch(&refused).is_none());
    assert_eq!(c.hello().unwrap(), [7; 32]);
    drop(c);
    assert_eq!(peer.join().unwrap().len(), 2);
}

/// A subscription reads its stream the same way: the first frame a broker in another
/// protocol sends — its refusal of the request that opened the stream — is a mismatch,
/// not a garbled delivery. `subscribe` meets it at its `IdleMarks` negotiation, a
/// request; `fork_subscribe` hands the connection over at once, so there the refusal
/// is read by the SUBSCRIPTION's decoder — the half that negotiation would otherwise
/// leave untested.
#[test]
fn a_subscription_reads_a_broker_in_another_protocol_as_a_mismatch() {
    let mut reply = encode_response(&Response::Error {
        code: ERR_REFUSED,
        msg: "malformed request".into(),
    });
    reply[0] = PROTO_VERSION + 1;
    let (ours, _peer) = scripted(vec![reply.clone()]);
    let err = Client::from_stream(ours)
        .subscribe(0, "/a/>")
        .err()
        .expect("mismatch");
    expect_mismatch(&err, PROTO_VERSION + 1, "subscribe negotiation");

    let (ours, _peer) = scripted(vec![reply]);
    let mut sub = Client::from_stream(ours)
        .fork_subscribe(0, "/a/fork", b"", "/a/>")
        .unwrap();
    expect_mismatch(
        &sub.recv().unwrap_err(),
        PROTO_VERSION + 1,
        "the subscription stream",
    );
}
