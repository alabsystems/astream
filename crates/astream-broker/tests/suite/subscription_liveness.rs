//! An idle subscription is not a silent one. A `Subscribe` or `SubscribeGroup` tail
//! that has caught up is sent a `Mark { next, head }` — once at once, then after every
//! idle interval with nothing written — so `Subscription::recv_live`, which arms a
//! read deadline on the first `Mark`, turns a link that died without a FIN into an
//! error instead of a reader parked for good; `recv` skips the marks, and `take`
//! stops on an idle one. Against a broker that never marks, `recv_live` never arms.
//! The subscribe asks for gap notices after the marks, and a broker that predates them
//! still tails.

#![cfg(unix)]

use astream_broker::proto::{
    decode_request, decode_response, encode_request, encode_response, read_frame, write_frame,
    Response, ERR_REFUSED,
};
use astream_broker::{
    connect, take, Broker, BrokerHandle, Client, Closer, Event, Request, Transport,
};
use std::io::{self, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::os::unix::net::UnixStream;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{mpsc, Arc};
use std::thread;
use std::time::Duration;

static CTR: AtomicU64 = AtomicU64::new(0);

/// A wait for something that must happen: a hang detector, never a latency budget.
const HANG: Duration = Duration::from_secs(60);

/// The idle interval these brokers mark at: short, so a test reaches its marks soon.
const IDLE: Duration = Duration::from_millis(50);

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
    let log = format!("/tmp/aslive_{pid}_{n}.log");
    let sock = format!("/tmp/aslive_{pid}_{n}.sock");
    let _ = std::fs::remove_file(&log);
    (Cleanup(vec![log.clone(), sock.clone()]), log, sock)
}

/// A broker that marks every [`IDLE`], over a Unix socket and over TCP, holding the
/// records `/a/x`@0, `/b/y`@1 and `/a/x`@2.
fn broker(log: &str, sock: &str) -> (Broker, BrokerHandle, BrokerHandle, String) {
    let b = Broker::open(log).unwrap();
    b.set_idle_mark(IDLE);
    let uds = b.serve(sock).unwrap();
    let tcp = b.serve_tcp("127.0.0.1:0").unwrap();
    let addr = tcp.tcp_addr().unwrap().to_string();
    let mut p = Client::connect(sock).unwrap();
    for (seq, subject) in [(1, "/a/x"), (2, "/b/y"), (3, "/a/x")] {
        p.publish(1, seq, subject, b"r").unwrap();
    }
    (b, uds, tcp, addr)
}

/// Every event a subscription reads, past the one it is waiting for, is a `Mark`.
fn next_delivery(sub: &mut astream_broker::AnySubscription) -> u64 {
    loop {
        match sub.recv_event().unwrap() {
            Some(Event::Delivery { offset, .. }) => return offset,
            Some(Event::Mark { .. }) => {}
            Some(Event::Gap(g)) => panic!("nothing is retained here, yet told {g:?}"),
            None => panic!("the broker closed"),
        }
    }
}

/// On both transports and both tailing verbs: the backlog, then a `Mark` at the head
/// the moment the tail catches up, then another after the idle interval with nothing
/// published; a later record still arrives as a delivery; and `recv` sees records
/// only.
#[test]
fn a_caught_up_tail_is_marked_at_once_and_again_when_idle() {
    let (_tmp, log, sock) = paths();
    let (_b, _uds, _tcp, addr) = broker(&log, &sock);
    let mut publisher = Client::connect(&sock).unwrap();
    let mut seq = 10;
    for (transport, endpoint) in [(Transport::Unix, sock.as_str()), (Transport::Tcp, &addr)] {
        for group in [None, Some("g")] {
            let what = format!("{transport:?} group={group:?}");
            let (c, closer) = connect(&transport, endpoint, None).unwrap();
            closer.set_read_timeout(Some(HANG)).unwrap();
            let mut sub = match group {
                None => c.subscribe(0, "/a/>").unwrap(),
                Some(g) => c.subscribe_group(g, "/a/>").unwrap(),
            };
            let (backlog, (_, head)) = publisher.fetch(0, "/a/>", 64).unwrap();
            for (offset, _, _) in &backlog {
                match sub.recv_event().unwrap().expect(&what) {
                    Event::Delivery { offset: got, .. } => assert_eq!(got, *offset, "{what}"),
                    other => panic!("{what}: the backlog first, got {other:?}"),
                }
            }
            for state in ["caught up", "idle"] {
                let e = sub.recv_event().unwrap().expect(&what);
                assert_eq!(
                    e,
                    Event::Mark {
                        next: head,
                        head,
                        durable: Some(head)
                    },
                    "{what}: {state}"
                );
            }
            seq += 1;
            let (off, _) = publisher.publish(1, seq, "/a/x", b"later").unwrap();
            assert_eq!(next_delivery(&mut sub), off, "{what}");
            closer.close();
        }
    }
    // `recv` is unchanged: the same stream, marks and all, reads as records only.
    let mut sub = Client::connect(&sock)
        .unwrap()
        .subscribe(0, "/a/>")
        .unwrap();
    sub.set_read_timeout(Some(HANG)).unwrap();
    for _ in 0..3 {
        assert!(sub.recv().unwrap().is_some());
    }
}

/// A legacy subscription never opted in to marks. Its socket's idle timeout must
/// still finish a quiet read: old `recv` skips Mark frames, so unsolicited marks
/// more frequent than that timeout keep an old take/drain parked indefinitely.
/// The timeout here is the behavior under test, not a latency assertion; all
/// deliveries and opted-in marks are awaited under the one-minute hang detector.
#[test]
fn legacy_subscriptions_stay_silent_while_new_subscriptions_opt_in() {
    let (_tmp, log, sock) = paths();
    let (_b, _uds, _tcp, addr) = broker(&log, &sock);
    let mut publisher = Client::connect(&sock).unwrap();
    let mut sequence = 0;
    for (transport, endpoint) in [(Transport::Unix, sock.as_str()), (Transport::Tcp, &addr)] {
        for group in [false, true] {
            sequence += 1;
            let what = format!("{transport:?} group={group}");
            let filter = format!("/quiet/{sequence}/>");
            let request = if group {
                Request::SubscribeGroup {
                    group: "legacy".into(),
                    filter: filter.clone(),
                }
            } else {
                Request::Subscribe {
                    from_offset: 0,
                    filter: filter.clone(),
                }
            };
            let (client, closer) = connect(&transport, endpoint, None).unwrap();
            let mut legacy = client.into_stream();
            // Longer than the broker's injected idle interval and liveness poll.
            closer
                .set_read_timeout(Some(Duration::from_millis(400)))
                .unwrap();
            write_frame(&mut legacy, &encode_request(&request)).unwrap();
            let err = read_frame(&mut legacy).expect_err(&what);
            assert!(
                matches!(
                    err.kind(),
                    io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut
                ),
                "{what}: {err}"
            );
            closer.set_read_timeout(Some(HANG)).unwrap();

            let (client, live_closer) = connect(&transport, endpoint, None).unwrap();
            live_closer.set_read_timeout(Some(HANG)).unwrap();
            let mut live = if group {
                client.subscribe_group("new", &filter).unwrap()
            } else {
                client.subscribe(0, &filter).unwrap()
            };
            for _ in 0..2 {
                assert!(
                    matches!(live.recv_event().unwrap(), Some(Event::Mark { .. })),
                    "{what}"
                );
            }
            let subject = format!("/quiet/{sequence}/x");
            let (offset, _) = publisher.publish(9, sequence, &subject, b"later").unwrap();
            assert!(
                matches!(
                    decode_response(&read_frame(&mut legacy).unwrap().expect(&what)),
                    Some(Response::Delivery { offset: got, .. }) if got == offset
                ),
                "{what}: legacy still receives deliveries"
            );
            assert_eq!(next_delivery(&mut live), offset, "{what}");
            closer.close();
            live_closer.close();
        }
    }
}

/// What a scripted peer knows of the subscribe's negotiation.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Peer {
    /// A broker that predates idle marks: it refuses `IdleMarks` as an unknown request,
    /// and is asked nothing more.
    Silent,
    /// A broker that marks a tail and predates gap notices: it refuses `GapNotices` as an
    /// unknown request.
    Marks,
    /// A broker that marks a tail and tells it what retention gave up below it.
    Gaps,
}

/// The `Error 5` an older broker answers a request it does not know with.
fn unknown_request() -> Response {
    Response::Error {
        code: ERR_REFUSED,
        msg: "malformed request".into(),
    }
}

/// The `Mark` a broker acknowledges a tail's opt-in with.
fn opted_in() -> Response {
    Response::Mark {
        next: 0,
        head: 0,
        resume: String::new(),
        durable: None,
        oldest: None,
    }
}

/// A scripted peer answers the subscribe's negotiation as `peer` would, then accepts the
/// subscription and hands back the framed stream.
fn scripted_subscription(peer: Peer) -> (astream_broker::Subscription, UnixStream) {
    let (ours, mut broker) = UnixStream::pair().unwrap();
    ours.set_read_timeout(Some(HANG)).unwrap();
    broker.set_read_timeout(Some(HANG)).unwrap();
    let negotiation = thread::spawn(move || {
        let mut answer = |asked: Request, known: bool| {
            let frame = read_frame(&mut broker).unwrap().unwrap();
            assert_eq!(decode_request(&frame), Some(asked), "{peer:?}");
            let reply = if known { opted_in() } else { unknown_request() };
            write_frame(&mut broker, &encode_response(&reply)).unwrap();
        };
        answer(Request::IdleMarks, peer != Peer::Silent);
        if peer != Peer::Silent {
            answer(Request::GapNotices, peer == Peer::Gaps);
        }
        let frame = read_frame(&mut broker).unwrap().unwrap();
        assert!(
            matches!(decode_request(&frame), Some(Request::Subscribe { .. })),
            "{peer:?}: the subscribe follows its negotiation"
        );
        broker
    });
    let sub = Client::from_stream(ours).subscribe(0, "/a/>").unwrap();
    sub.set_read_timeout(None).unwrap();
    (sub, negotiation.join().unwrap())
}

/// GAP NOTICES ARE NEGOTIATED as idle marks are (REQUIREMENTS R4, addendum A9): after idle
/// marks the subscribe asks for them; a broker that predates idle marks is not asked
/// (`Silent`: its next frame is the subscribe), and one that marks but predates notices
/// refuses the ask as an unknown request, the tail running as before. One that knows them
/// sends a notice: `recv` skips it to the record behind it and keeps it for `take_gap`,
/// and `recv_event` returns it. NC: a `gap_notices` that propagates the older broker's
/// refusal fails the subscribe against `Marks`.
#[test]
fn gap_notices_are_negotiated_and_an_older_broker_still_tails() {
    let delivery = |offset| Response::Delivery {
        offset,
        subject: "/a/x".into(),
        body: b"mail".to_vec(),
    };
    let told = astream_broker::Gap {
        from: 0,
        to: 2,
        records: Some(2),
    };
    for peer in [Peer::Silent, Peer::Marks, Peer::Gaps] {
        let (mut sub, mut broker) = scripted_subscription(peer);
        if peer == Peer::Gaps {
            write_frame(&mut broker, &encode_response(&Response::Gap(told))).unwrap();
        }
        write_frame(&mut broker, &encode_response(&delivery(2))).unwrap();
        let got = sub.recv().unwrap().expect("the tail delivers");
        assert_eq!(got, (2, "/a/x".to_string(), b"mail".to_vec()), "{peer:?}");
        let expect = (peer == Peer::Gaps).then_some(told);
        assert_eq!(
            sub.take_gap(),
            expect,
            "{peer:?}: what the skipping read passed"
        );
        assert_eq!(sub.take_gap(), None, "{peer:?}: taken once");
        if peer == Peer::Gaps {
            let later = astream_broker::Gap {
                from: 3,
                to: 5,
                records: None,
            };
            write_frame(&mut broker, &encode_response(&Response::Gap(later))).unwrap();
            assert_eq!(sub.recv_event().unwrap(), Some(Event::Gap(later)));
        }
    }
}

/// `take` stops when the broker says the subscription is idle, so a caller with NO
/// idle window of its own (or one longer than the broker's interval) gets what has
/// arrived instead of parking; the catch-up mark ahead of a record published after
/// the subscribe does not end the take before that record.
#[test]
fn take_stops_on_an_idle_mark_and_not_on_the_catch_up_mark() {
    let (_tmp, log, sock) = paths();
    let (_b, _uds, _tcp, _addr) = broker(&log, &sock);
    let (c, closer) = connect(&Transport::Unix, &sock, None).unwrap();
    let mut sub = c.subscribe_group("g", "/b/>").unwrap();
    let mut publisher = Client::connect(&sock).unwrap();
    publisher.publish(1, 20, "/b/z", b"after").unwrap();
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        let _ = tx.send(take(&mut sub, 64));
    });
    let got = rx.recv_timeout(HANG).unwrap_or_else(|_| {
        closer.close();
        panic!("take parked on an idle subscription")
    });
    let subjects: Vec<String> = got.unwrap().into_iter().map(|r| r.1).collect();
    assert_eq!(subjects, ["/b/y", "/b/z"]);
}

/// Marks that piled up while nobody was taking say nothing about NOW: a take that
/// finds them queued ahead of records passes over them and takes the records.
#[test]
fn take_passes_over_marks_already_queued() {
    let (mut sub, mut broker) = scripted_subscription(Peer::Silent);
    let mark = Response::Mark {
        next: 0,
        head: 0,
        resume: String::new(),
        durable: None,
        oldest: None,
    };
    for _ in 0..4 {
        write_frame(&mut broker, &encode_response(&mark)).unwrap();
    }
    for offset in [0, 1] {
        let d = Response::Delivery {
            offset,
            subject: "/a/x".into(),
            body: vec![],
        };
        write_frame(&mut broker, &encode_response(&d)).unwrap();
    }
    broker.shutdown(std::net::Shutdown::Write).unwrap();
    let got: Vec<u64> = take(&mut sub, 64)
        .unwrap()
        .into_iter()
        .map(|r| r.0)
        .collect();
    assert_eq!(got, [0, 1]);
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

/// Over a link that goes silent without a FIN, `recv_live` armed by the broker's
/// marks fails with a timeout — where `recv` would park for good.
#[test]
fn recv_live_turns_a_frozen_link_into_an_error() {
    let (_tmp, log, sock) = paths();
    let (_b, _uds, _tcp, addr) = broker(&log, &sock);
    let frozen = Arc::new(AtomicBool::new(false));
    let (c, closer) = connect(&Transport::Tcp, &relay(addr, frozen.clone()), None).unwrap();
    let mut sub = c.subscribe(0, "/a/>").unwrap();
    let closer = Arc::new(closer);
    let (tx, rx) = mpsc::channel();
    let (armed_tx, armed_rx) = mpsc::channel();
    let (resume_tx, resume_rx) = mpsc::channel();
    let reader = closer.clone();
    let reader_thread = thread::spawn(move || {
        // Deliveries do not arm a legacy-compatible subscription. Observe the
        // actual Mark through the API that arms its deadline before freezing.
        loop {
            match sub.recv_live_event(&reader, Duration::from_millis(500)) {
                Ok(Some(Event::Delivery { offset, .. })) => {
                    if tx.send(Ok(Some(offset))).is_err() {
                        return;
                    }
                }
                Ok(Some(Event::Mark { next, head, .. })) => {
                    let _ = armed_tx.send((next, head));
                    break;
                }
                Ok(Some(Event::Gap(g))) => panic!("nothing is retained here, yet told {g:?}"),
                Ok(None) => {
                    let _ = tx.send(Ok(None));
                    return;
                }
                Err(error) => {
                    let _ = tx.send(Err(error));
                    return;
                }
            }
        }
        // Start the recv_live check only after the main thread freezes the
        // relay; a timeout from before the freeze cannot satisfy the test.
        if resume_rx.recv_timeout(HANG).is_err() {
            return;
        }
        loop {
            let r = sub.recv_live(&reader, Duration::from_millis(500));
            let done = r.is_err() || matches!(r, Ok(None));
            let _ = tx.send(r.map(|rec| rec.map(|rec| rec.0)));
            if done {
                return;
            }
        }
    });
    for want in [0, 2] {
        assert_eq!(rx.recv_timeout(HANG).unwrap().unwrap(), Some(want));
    }
    let mark = armed_rx.recv_timeout(HANG).unwrap_or_else(|_| {
        closer.close();
        panic!("the broker never armed the subscription with a Mark")
    });
    assert_eq!(mark, (3, 3), "the tail caught up before it was frozen");
    frozen.store(true, Ordering::Relaxed);
    resume_tx.send(()).unwrap();
    let err = rx
        .recv_timeout(HANG)
        .unwrap_or_else(|_| {
            closer.close();
            panic!("recv_live parked on a frozen link")
        })
        .unwrap_err();
    assert!(
        matches!(
            err.kind(),
            io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut
        ),
        "{err}"
    );
    reader_thread.join().unwrap();
}

/// The version check: a broker that never marks a tail never arms the deadline, so
/// `recv_live` against it is `recv`; the first `Mark` arms it.
#[test]
fn recv_live_arms_only_on_a_mark() {
    for peer in [Peer::Silent, Peer::Marks] {
        let (mut sub, mut broker) = scripted_subscription(peer);
        let closer: Closer = sub.closer().unwrap();
        let deadline = Duration::from_secs(7);
        let delivery = |offset| Response::Delivery {
            offset,
            subject: "/a/x".into(),
            body: vec![],
        };
        write_frame(&mut broker, &encode_response(&delivery(0))).unwrap();
        assert_eq!(sub.recv_live(&closer, deadline).unwrap().unwrap().0, 0);
        assert_eq!(
            sub.get_ref().read_timeout().unwrap(),
            None,
            "no mark, no deadline"
        );

        let mark = Response::Mark {
            next: 1,
            head: 1,
            resume: String::new(),
            durable: None,
            oldest: None,
        };
        write_frame(&mut broker, &encode_response(&mark)).unwrap();
        write_frame(&mut broker, &encode_response(&delivery(1))).unwrap();
        assert_eq!(sub.recv_live(&closer, deadline).unwrap().unwrap().0, 1);
        assert_eq!(sub.get_ref().read_timeout().unwrap(), Some(deadline));
    }
}

/// `recv_live_event` is `recv_live` that RETURNS each `Mark`, armed on it: a delivery
/// before any mark arms nothing; a mark comes back with its durable head (and the
/// subscription keeps it), the deadline armed by then; a broker that marked and hung up
/// is read, mark then close, never an error.
#[test]
fn recv_live_event_returns_each_mark_armed_on_it() {
    let (mut sub, mut broker) = scripted_subscription(Peer::Marks);
    let closer: Closer = sub.closer().unwrap();
    let deadline = Duration::from_secs(7);
    let delivery = |offset| Response::Delivery {
        offset,
        subject: "/a/x".into(),
        body: vec![],
    };
    write_frame(&mut broker, &encode_response(&delivery(0))).unwrap();
    assert!(matches!(
        sub.recv_live_event(&closer, deadline).unwrap(),
        Some(Event::Delivery { offset: 0, .. })
    ));
    assert_eq!(
        sub.get_ref().read_timeout().unwrap(),
        None,
        "no mark, no deadline"
    );
    let mark = Response::Mark {
        next: 1,
        head: 1,
        resume: String::new(),
        durable: Some(1),
        oldest: None,
    };
    write_frame(&mut broker, &encode_response(&mark)).unwrap();
    assert!(matches!(
        sub.recv_live_event(&closer, deadline).unwrap(),
        Some(Event::Mark {
            next: 1,
            durable: Some(1),
            ..
        })
    ));
    assert_eq!(sub.get_ref().read_timeout().unwrap(), Some(deadline));
    assert_eq!(sub.seen_durable(), Some(1), "the subscription kept it");
    write_frame(&mut broker, &encode_response(&mark)).unwrap();
    drop(broker);
    assert!(
        matches!(
            sub.recv_live_event(&closer, deadline)
                .expect("a mark from a broker that then hung up"),
            Some(Event::Mark { .. })
        ),
        "the mark, not the re-arm's refusal on the shut socket"
    );
    assert!(sub.recv_live_event(&closer, deadline).unwrap().is_none());
}

/// A broker that sent a `Mark` and a record and hung up BEFORE `recv_live` re-arms
/// its deadline on that mark: the subscription still reads the record, then the
/// close. macOS takes no socket option on a socket shut down both ways
/// (`setsockopt` fails `EINVAL`), and the re-arm used to fail the call with a bare
/// "Invalid argument (os error 22)", losing the record the broker had sent. The
/// broker side runs on this thread and is gone before the re-arm, so the interleaving
/// is the one a race only sometimes produced. Every other bound on the hung-up socket
/// is no error either, and a zero bound is still std's refusal.
#[test]
fn recv_live_reads_a_broker_that_marked_and_hung_up_then_the_close() {
    let (mut sub, mut broker) = scripted_subscription(Peer::Marks);
    let closer: Closer = sub.closer().unwrap();
    let mark = Response::Mark {
        next: 7,
        head: 7,
        resume: String::new(),
        durable: None,
        oldest: None,
    };
    let record = Response::Delivery {
        offset: 7,
        subject: "/a/x".into(),
        body: b"mail".to_vec(),
    };
    write_frame(&mut broker, &encode_response(&mark)).unwrap();
    write_frame(&mut broker, &encode_response(&record)).unwrap();
    drop(broker);
    let got = sub
        .recv_live(&closer, Duration::from_secs(7))
        .expect("the record the broker sent before it hung up");
    assert_eq!(got, Some((7, "/a/x".to_string(), b"mail".to_vec())));
    assert_eq!(
        sub.recv_live(&closer, Duration::from_secs(7))
            .expect("then the close"),
        None,
        "the broker hung up"
    );
    closer
        .set_read_timeout(None)
        .expect("a hung-up socket has no read to bound");
    closer.set_write_timeout(Some(HANG)).expect("nor a write");
    sub.set_read_timeout(Some(HANG))
        .expect("nor the subscription's own read");
    for zero in [
        closer.set_read_timeout(Some(Duration::ZERO)),
        closer.set_write_timeout(Some(Duration::ZERO)),
        sub.set_read_timeout(Some(Duration::ZERO)),
    ] {
        assert_eq!(
            zero.expect_err("a zero bound is still refused").kind(),
            io::ErrorKind::InvalidInput
        );
    }
}
