//! A GUARDED broker bounds how long a connection may stay unauthenticated.
//!
//! On a guarded broker everything short of an accepted capability — `Hello`, a
//! refused `Attach`, any verb an empty keyring does not authorize — is free for
//! anyone to send. So the first-frame deadline cannot end at the first frame there:
//! it runs from accept until an `Attach` is accepted, and a connection that has not
//! attached by then is refused and closed. Otherwise a peer that sends `Hello` and
//! waits holds a connection slot for as long as it likes, and a handful of them lock
//! every legitimate client out at the connection cap.
//!
//! An UNGUARDED broker has nothing to authenticate and still lifts the deadline at
//! the first frame.

#![cfg(all(unix, feature = "cap"))]

use astream_broker::proto::{decode_response, encode_request, read_frame, write_frame};
use astream_broker::{Broker, Client, Request, Response};
use astream_cap::mint;
use std::io::{Read, Write};
use std::os::unix::net::UnixStream;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

static CTR: AtomicU64 = AtomicU64::new(0);
const SECRET: &[u8] = b"core2-guarded-preauth";
/// The first-frame timeout every test here runs under.
const DEADLINE: Duration = Duration::from_millis(300);
/// How long a test waits for the broker to close a connection before calling it held.
const PATIENCE: Duration = Duration::from_secs(5);

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
    let log = format!("/tmp/ascore2_pa_{pid}_{n}.log");
    let _ = std::fs::remove_file(&log);
    let sock = format!("/tmp/ascore2_pa_{pid}_{n}.sock");
    (Cleanup::new(&[&log, &sock]), log, sock)
}

fn guarded() -> (Cleanup, Broker, String) {
    let (tmp, log, sock) = paths();
    let b = Broker::open_guarded(&log, SECRET.to_vec()).unwrap();
    b.set_first_frame_timeout(DEADLINE);
    (tmp, b, sock)
}

/// Read responses from `s` until the broker closes it, or `PATIENCE` passes. Returns
/// whether it closed, and the error messages read on the way.
fn read_until_closed<S: Read>(s: &mut S) -> (bool, Vec<String>) {
    let t = Instant::now();
    let mut errors = Vec::new();
    while t.elapsed() < PATIENCE {
        match read_frame(s) {
            Ok(None) => return (true, errors),
            Ok(Some(p)) => {
                if let Some(Response::Error { msg, .. }) = decode_response(&p) {
                    errors.push(msg);
                }
            }
            Err(e)
                if matches!(
                    e.kind(),
                    std::io::ErrorKind::WouldBlock | std::io::ErrorKind::TimedOut
                ) =>
            {
                return (false, errors); // the read timeout: still open
            }
            Err(_) => return (true, errors), // reset: closed
        }
    }
    (false, errors)
}

fn hello_then_idle(sock: &str) -> UnixStream {
    let mut c = Client::connect(sock).unwrap();
    c.hello().unwrap();
    let s = c.into_stream();
    s.set_read_timeout(Some(PATIENCE)).unwrap();
    s
}

/// The refusal a connection that never attached is sent before it is closed.
fn is_preauth_refusal(errors: &[String]) -> bool {
    errors
        .iter()
        .any(|m| m.contains("unauthorized") && m.contains("no capability attached"))
}

/// `Hello` is a complete frame that needs no capability. It must not stop the clock.
#[test]
fn a_connection_that_says_hello_and_waits_is_refused_at_the_deadline() {
    let (_tmp, b, sock) = guarded();
    let mut h = b.serve(&sock).unwrap();

    let mut idle = hello_then_idle(&sock);
    let t = Instant::now();
    let (closed, errors) = read_until_closed(&mut idle);
    assert!(
        closed,
        "a guarded connection that only said Hello was still open after {:?}",
        t.elapsed()
    );
    assert!(
        is_preauth_refusal(&errors),
        "closed without saying why: {errors:?}"
    );

    h.shutdown();
}

/// The deadline is counted from accept, not re-armed per frame: a peer that keeps
/// sending frames no capability authorizes — `Hello`s, a forged `Attach`, a publish —
/// is closed on the same schedule as a silent one.
#[test]
fn a_peer_that_keeps_talking_without_attaching_is_closed_on_the_same_deadline() {
    let (_tmp, b, sock) = guarded();
    let mut h = b.serve(&sock).unwrap();

    let mut s = UnixStream::connect(&sock).unwrap();
    s.set_read_timeout(Some(Duration::from_millis(50))).unwrap();
    let requests = [
        Request::Hello,
        Request::Attach {
            grant: "rw:/>".to_string(),
            proof: vec![0u8; 32],
        },
        Request::Publish {
            producer_id: 1,
            producer_seq: 0,
            subject: "/a/x".to_string(),
            body: b"m".to_vec(),
        },
    ];
    let t = Instant::now();
    let mut errors = Vec::new();
    let mut closed = false;
    'talk: for req in requests.iter().cycle() {
        if t.elapsed() > PATIENCE {
            break;
        }
        if write_frame(&mut s, &encode_request(req)).is_err() {
            closed = true;
            break;
        }
        // Drain what came back; EOF or a reset is the broker closing the connection.
        loop {
            match read_frame(&mut s) {
                Ok(None) => {
                    closed = true;
                    break 'talk;
                }
                Ok(Some(p)) => {
                    if let Some(Response::Error { msg, .. }) = decode_response(&p) {
                        errors.push(msg);
                    }
                }
                Err(e)
                    if matches!(
                        e.kind(),
                        std::io::ErrorKind::WouldBlock | std::io::ErrorKind::TimedOut
                    ) =>
                {
                    break
                }
                Err(_) => {
                    closed = true;
                    break 'talk;
                }
            }
        }
    }
    assert!(
        closed,
        "a peer that never attached kept its connection for {:?} by talking",
        t.elapsed()
    );
    assert!(t.elapsed() < PATIENCE);

    h.shutdown();
}

/// Nor does a frame sent a byte at a time: the time left bounds each read, so a
/// frame that would take several deadlines to arrive is cut off at the first.
#[test]
fn a_frame_sent_a_byte_at_a_time_does_not_stretch_the_deadline() {
    let (_tmp, b, sock) = guarded();
    let mut h = b.serve(&sock).unwrap();

    let frame = {
        let mut out = Vec::new();
        let payload = encode_request(&Request::Publish {
            producer_id: 1,
            producer_seq: 0,
            subject: "/a/x".to_string(),
            body: vec![b'm'; 100],
        });
        write_frame(&mut out, &payload).unwrap();
        out
    };
    let mut s = UnixStream::connect(&sock).unwrap();
    s.set_read_timeout(Some(Duration::from_millis(20))).unwrap();
    let t = Instant::now();
    let mut sent = 0;
    let mut closed = false;
    while sent < frame.len() {
        if s.write_all(&frame[sent..=sent]).is_err() {
            closed = true;
            break;
        }
        sent += 1;
        // The 20 ms read timeout paces the trickle; EOF or a frame is the broker.
        match read_frame(&mut s) {
            Err(e)
                if matches!(
                    e.kind(),
                    std::io::ErrorKind::WouldBlock | std::io::ErrorKind::TimedOut
                ) => {}
            _ => {
                closed = true;
                break;
            }
        }
    }
    if !closed {
        s.set_read_timeout(Some(PATIENCE)).unwrap();
        closed = read_until_closed(&mut s).0;
    }
    assert!(
        closed && sent < frame.len(),
        "a {}-byte frame trickled over {:?} was still being read ({sent} bytes in) \
         past the {DEADLINE:?} deadline",
        frame.len(),
        t.elapsed()
    );

    h.shutdown();
}

/// The attack itself: peers that never authenticate cannot hold the connection cap.
/// Once their deadline passes their slots are free, and a client with a capability
/// gets in.
#[test]
fn unauthenticated_peers_do_not_keep_the_connection_cap() {
    let (_tmp, b, sock) = guarded();
    b.set_max_conns(2);
    let mut h = b.serve(&sock).unwrap();

    let mut squatters = [hello_then_idle(&sock), hello_then_idle(&sock)];
    for s in &mut squatters {
        let (closed, _) = read_until_closed(s);
        assert!(closed, "an unauthenticated connection kept its slot");
    }

    let god = mint(SECRET, "rw:/>").unwrap();
    let mut c = Client::connect(&sock).unwrap();
    c.attach(&god.filter, &god.tag)
        .expect("a capability holder was locked out by peers that never authenticated");
    assert_eq!(c.publish(1, 0, "/a/x", b"m").unwrap(), (0, false));

    h.shutdown();
}

/// An ACCEPTED capability ends the pre-authentication phase: an attached connection
/// that then idles well past the deadline is still served.
#[test]
fn an_attached_connection_is_not_on_a_timer() {
    let (_tmp, b, sock) = guarded();
    let mut h = b.serve(&sock).unwrap();

    let god = mint(SECRET, "rw:/>").unwrap();
    let mut c = Client::connect(&sock).unwrap();
    // A refused attach first: it must not count as authenticating, nor lose the
    // connection the chance to attach properly within the deadline.
    assert!(c.attach(&god.filter, &[7u8; 32]).is_err());
    c.attach(&god.filter, &god.tag).unwrap();
    std::thread::sleep(DEADLINE * 3);
    assert_eq!(c.publish(1, 0, "/a/x", b"m").unwrap(), (0, false));

    h.shutdown();
}

/// An UNGUARDED broker keeps lifting the deadline at the first frame: there is no
/// capability to wait for, so a quiet client that has spoken once stays connected.
#[test]
fn an_unguarded_broker_still_lifts_the_deadline_at_the_first_frame() {
    let (_tmp, log, sock) = paths();
    let b = Broker::open(&log).unwrap();
    b.set_first_frame_timeout(DEADLINE);
    let mut h = b.serve(&sock).unwrap();

    let mut c = Client::connect(&sock).unwrap();
    c.hello().unwrap();
    std::thread::sleep(DEADLINE * 3);
    assert_eq!(c.publish(1, 0, "/a/x", b"m").unwrap(), (0, false));

    h.shutdown();
}

/// The sealed transport runs the same deadline after its handshake: holding the
/// transport key proves nothing about capabilities.
#[cfg(feature = "aead")]
#[test]
fn a_sealed_connection_that_never_attaches_is_refused_at_the_deadline() {
    const KEY: [u8; 32] = [0x5a; 32];
    let (_tmp, b, _) = guarded();
    let mut h = b.serve_tcp_sealed("127.0.0.1:0", KEY).unwrap();
    let addr = h.tcp_addr().unwrap().to_string();

    let mut c = Client::connect_tcp_sealed(&addr, KEY).unwrap();
    c.hello().unwrap();
    let mut s = c.into_stream();
    s.get_ref().set_read_timeout(Some(PATIENCE)).unwrap();
    let (closed, errors) = read_until_closed(&mut s);
    assert!(closed, "a sealed, unattached connection was never closed");
    assert!(
        is_preauth_refusal(&errors),
        "closed without saying why: {errors:?}"
    );

    // An attached sealed client is served past the deadline.
    let god = mint(SECRET, "rw:/>").unwrap();
    let mut c = Client::connect_tcp_sealed(&addr, KEY).unwrap();
    c.attach(&god.filter, &god.tag).unwrap();
    std::thread::sleep(DEADLINE * 3);
    assert_eq!(c.publish(1, 0, "/a/x", b"m").unwrap(), (0, false));

    h.shutdown();
}
