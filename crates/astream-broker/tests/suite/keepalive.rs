//! A request/reply connection that KEEPS ALIVE is one the broker can tell is dead.
//!
//! The broker writes to a request/reply connection only to answer it, so a client that
//! vanished without a FIN — a power loss, a path that died while the link was idle —
//! used to leave its connection thread parked in a read nothing ended: its will never
//! fired and its slot was never freed until the broker restarted. A client that sends
//! `Keepalive` asks to be held to the broker's keepalive deadline instead, and a TCP
//! connection that then goes silent that long is ended exactly as a closed one is: its
//! will fires. The deadline is armed by the first `Keepalive`, so a client that never
//! sends one is never cut, and a Unix-socket connection is never held to it at all.

#![cfg(unix)]

use astream_broker::proto::{
    decode_request, encode_response, read_frame, write_frame, ERR_REFUSED,
};
use astream_broker::{Broker, Client, Request, Response};
use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::os::unix::net::UnixStream;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::Duration;

static CTR: AtomicU64 = AtomicU64::new(0);

/// A wait for something that must happen: a hang detector, never a latency budget.
const HANG: Duration = Duration::from_secs(60);

/// The keepalive deadline the broker here holds connections to: short, so the one
/// connection that goes silent is ended soon.
const DEADLINE: Duration = Duration::from_millis(200);

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
    let log = format!("/tmp/askeep_{pid}_{n}.log");
    let sock = format!("/tmp/askeep_{pid}_{n}.sock");
    let _ = std::fs::remove_file(&log);
    (Cleanup(vec![log.clone(), sock.clone()]), log, sock)
}

/// A TCP relay that can FREEZE: from then on it forwards nothing and closes nothing —
/// the half-open link a power loss or a network change leaves behind.
fn relay(to: String, frozen: Arc<AtomicBool>) -> String {
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let addr = listener.local_addr().unwrap().to_string();
    thread::spawn(move || {
        let (client, _) = listener.accept().unwrap();
        let broker = TcpStream::connect(to).unwrap();
        let halves = [
            (client.try_clone().unwrap(), broker.try_clone().unwrap()),
            (broker, client),
        ];
        for (mut from, mut into) in halves {
            let frozen = frozen.clone();
            thread::spawn(move || {
                let mut buf = [0u8; 4096];
                loop {
                    let n = match from.read(&mut buf) {
                        Ok(0) | Err(_) => return,
                        Ok(n) => n,
                    };
                    if !frozen.load(Ordering::Relaxed) && into.write_all(&buf[..n]).is_err() {
                        return;
                    }
                }
            });
        }
    });
    addr
}

/// Register a will that publishes `gone` to `/n/<name>/presence` under `producer`.
fn will(c: &mut Client<impl Read + Write>, producer: u64, name: &str) {
    c.will(producer, 1, &format!("/n/{name}/presence"), b"gone")
        .unwrap();
}

/// THE DEAD PEER, AND THE TWO LIVE ONES IT MUST NOT TAKE WITH IT. Three idle
/// connections hold wills: a TCP one that never keeps alive, a Unix one that does, and
/// a TCP one that keeps alive through a relay that then freezes without a FIN. Only the
/// frozen one is ended — its will is the first to fire, and the only one on the log —
/// although the other two have been idle longer: they went quiet before it did, so had
/// either been held to the deadline its will would have fired first. Both still answer.
#[test]
fn a_kept_alive_connection_that_goes_silent_is_ended_and_its_will_fires() {
    let (_tmp, log, sock) = paths();
    let b = Broker::open(&log).unwrap();
    b.set_keepalive_deadline(DEADLINE);
    // No idle marks inside the hang detector: `recv` below skips marks, and one
    // every interval would keep it from ever timing out.
    b.set_idle_mark(HANG * 2);
    let _uds = b.serve(&sock).unwrap();
    let tcp = b.serve_tcp("127.0.0.1:0").unwrap();
    let addr = tcp.tcp_addr().unwrap().to_string();
    let mut wills = Client::connect(&sock)
        .unwrap()
        .subscribe(0, "/n/>")
        .unwrap();
    wills.set_read_timeout(Some(HANG)).unwrap();

    let mut quiet = Client::connect_tcp(&addr).unwrap();
    will(&mut quiet, 2, "quiet");
    let mut local = Client::connect(&sock).unwrap();
    will(&mut local, 3, "local");
    assert!(local.keepalive().unwrap(), "the broker knows the verb");
    let frozen = Arc::new(AtomicBool::new(false));
    let mut gone = Client::connect_tcp(relay(addr, frozen.clone())).unwrap();
    will(&mut gone, 1, "gone");
    assert!(gone.keepalive().unwrap());
    frozen.store(true, Ordering::Relaxed);

    let (_, first, body) = wills.recv().unwrap().expect("the broker closed");
    assert_eq!(
        (first.as_str(), body.as_slice()),
        ("/n/gone/presence", &b"gone"[..])
    );
    let (face, _) = Client::connect(&sock).unwrap().last_all("/n/>").unwrap();
    let fired: Vec<&str> = face.iter().map(|r| r.1.as_str()).collect();
    assert_eq!(fired, ["/n/gone/presence"]);
    quiet.fetch(0, "/n/>", 0).unwrap();
    assert!(local.keepalive().unwrap());
}

/// A scripted broker on the other end of `ours`: it answers each request it reads with
/// the next of `replies`, and hands back every request it read once `ours` closes.
fn scripted(replies: Vec<Response>) -> (UnixStream, thread::JoinHandle<Vec<Request>>) {
    let (ours, mut theirs) = UnixStream::pair().unwrap();
    ours.set_read_timeout(Some(HANG)).unwrap();
    theirs.set_read_timeout(Some(HANG)).unwrap();
    let peer = thread::spawn(move || {
        let mut replies = replies.into_iter();
        let mut read = Vec::new();
        while let Ok(Some(p)) = read_frame(&mut theirs) {
            read.push(decode_request(&p).expect("a request in this protocol"));
            if let Some(reply) = replies.next() {
                write_frame(&mut theirs, &encode_response(&reply)).unwrap();
            }
        }
        read
    });
    (ours, peer)
}

fn mark() -> Response {
    Response::Mark {
        next: 4,
        head: 4,
        resume: String::new(),
        durable: None,
        oldest: None,
    }
}

/// `keepalive_if_idle` sends a keepalive only on a connection that has sent nothing for
/// the interval: not on one just made, and not right after a request.
#[test]
fn keepalive_if_idle_sends_only_on_an_idle_connection() {
    let (ours, peer) = scripted(vec![mark()]);
    let mut c = Client::from_stream(ours);
    let hour = Duration::from_secs(3600);
    assert!(!c.keepalive_if_idle(hour).unwrap(), "just made");
    assert!(c.keepalive_if_idle(Duration::ZERO).unwrap(), "idle");
    assert!(!c.keepalive_if_idle(hour).unwrap(), "just sent");
    drop(c);
    assert_eq!(peer.join().unwrap(), [Request::Keepalive]);
}

/// The version check: a broker that predates the verb answers it "malformed request",
/// a whole reply, so `keepalive` is `false`, the client stays in step, and
/// `keepalive_if_idle` sends nothing more — such a broker never cuts the connection.
#[test]
fn a_broker_that_predates_keepalive_is_not_kept_alive() {
    let malformed = Response::Error {
        code: ERR_REFUSED,
        msg: "malformed request".into(),
    };
    let nonce = Response::Nonce {
        nonce: vec![7; 32],
        log: None,
        ext: astream_broker::NonceExt::default(),
    };
    let (ours, peer) = scripted(vec![malformed, nonce]);
    let mut c = Client::from_stream(ours);
    assert!(!c.keepalive().unwrap());
    assert!(!c.keepalive_if_idle(Duration::ZERO).unwrap());
    assert_eq!(c.hello().unwrap(), [7; 32], "in step");
    drop(c);
    assert_eq!(peer.join().unwrap(), [Request::Keepalive, Request::Hello]);
}

/// On a guarded broker a keepalive needs a capability attached: its `Mark` names the
/// log's head, which an unattached connection is told nothing about. The refusal is a
/// whole reply; once a grant is attached the same connection keeps alive.
#[cfg(feature = "cap")]
#[test]
fn a_guarded_keepalive_needs_a_capability() {
    use astream_broker::broker_refusal;
    use astream_broker::proto::ERR_UNAUTHORIZED;
    const SECRET: &[u8] = b"keepalive-guarded";
    let (_tmp, log, sock) = paths();
    let b = Broker::open_guarded(&log, SECRET.to_vec()).unwrap();
    let _uds = b.serve(&sock).unwrap();
    let mut c = Client::connect(&sock).unwrap();
    let refused = c.keepalive().unwrap_err();
    assert_eq!(
        broker_refusal(&refused).map(|r| r.code),
        Some(ERR_UNAUTHORIZED),
        "{refused}"
    );
    let cap = astream_cap::mint(SECRET, "ro:/n/>").unwrap();
    c.attach(&cap.filter, &cap.tag).unwrap();
    assert!(c.keepalive().unwrap());
}
