// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Signals over a real broker and a socket. Every wait is a one-minute hang detector on
//! something that must happen (a frame, a channel send, a row leaving the table); nothing
//! sleeps. That something was NOT sent is shown by what the next frame is (a `Mark`, a
//! sentinel signal put after it), never by a quiet interval.

use super::*;
use crate::proto::{decode_request, read_frame, NonceExt, REQUEST_FRESH_PUBLISH, REQUEST_SETTLE};
use crate::test_scratch::Scratch;
use crate::{broker_refusal, Client, Signal, SignalEvent, SignalSubscription};

const HANG: Duration = Duration::from_secs(60);

fn timed(stream: UnixStream) -> UnixStream {
    stream.set_read_timeout(Some(HANG)).unwrap();
    stream.set_write_timeout(Some(HANG)).unwrap();
    stream
}

fn client(socket: &Path) -> Client {
    let mut client = Client::from_stream(timed(UnixStream::connect(socket).unwrap()));
    client.hello().unwrap();
    client
}

fn signals(socket: &Path, filter: &str) -> SignalSubscription<UnixStream> {
    client(socket).subscribe_signals(filter).unwrap()
}

fn sig(subject: &str, producer_id: u64, seq: u64, body: &[u8]) -> Signal {
    Signal {
        producer_id,
        seq,
        subject: subject.to_string(),
        body: body.to_vec(),
    }
}

/// Read a stream's first drain: every signal up to its first mark.
fn first_drain(sub: &mut SignalSubscription<UnixStream>) -> Vec<Signal> {
    let mut out = Vec::new();
    while let SignalEvent::Signal(s) = sub.recv_event().unwrap().expect("the broker closed") {
        out.push(s);
    }
    out
}

/// The class of the refusal `e` is.
fn code(e: &io::Error) -> u8 {
    match broker_refusal(e) {
        Some(refusal) => refusal.code,
        None => panic!("not a broker refusal: {e}"),
    }
}

/// How many subjects the broker holds a signal for.
fn held(broker: &Broker) -> usize {
    lock_signals(&broker.shared).len()
}

/// Wait for the broker to hold `want` signals: the end of a connection is noticed by its
/// own thread, some time after the client's side closed.
fn await_held(broker: &Broker, want: usize) {
    let started = Instant::now();
    while held(broker) != want {
        assert!(
            started.elapsed() < HANG,
            "the broker still holds {} signals, not {want}",
            held(broker)
        );
        thread::yield_now();
    }
}

/// Every file under `dir` with its bytes (`None` for what is no regular file: the socket).
fn files(dir: &Path, out: &mut Vec<(std::path::PathBuf, Option<Vec<u8>>)>) {
    for entry in std::fs::read_dir(dir).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        let kind = entry.file_type().unwrap();
        if kind.is_dir() {
            files(&path, out);
        } else if kind.is_file() {
            let bytes = std::fs::read(&path).unwrap();
            out.push((path, Some(bytes)));
        } else {
            out.push((path, None));
        }
    }
}

/// Everything an append would move: the log's heads, its flush and writer counts, its
/// own statistics, and every byte of every file in the broker's folder.
fn written(broker: &Broker, root: &Path) -> impl PartialEq + std::fmt::Debug {
    let stats = broker.stats();
    let mut on_disk = Vec::new();
    files(root, &mut on_disk);
    on_disk.sort();
    (
        (broker.head(), broker.visible_head(), broker.durable_head()),
        broker.flush_counts(),
        stats.log,
        (
            stats.writer_batches,
            stats.writer_round_trips,
            stats.empty_batches,
        ),
        on_disk,
    )
}

/// THE PACKAGE'S EXIT TEST (aterm tracker AF-15). A producer signals a subject a hundred
/// times, and two more, while a subscriber is held where a slow one sits (its first drain
/// written, nothing read since). Then:
///
/// - NOTHING WAS APPENDED: the log's heads, its flush and writer counts, its statistics and
///   every byte of every file in the broker's folder are what they were after the one
///   control record published first, and `Fetch` and `Last` find that record alone.
/// - THE SLOW SUBSCRIBER GETS ONLY THE NEWEST: released, it reads each subject once, at its
///   last value, and then the sentinel put after it; none of the values it missed.
/// - AN EARLIER INCARNATION'S LATE SIGNAL, from a second connection of the same producer at
///   a lower seq, changes nothing a reader is sent.
/// - NOTHING IS RETAINED: the broker restarted on the same log holds one record and no
///   signal.
///
/// NC: were a signal a publish, the heads would have moved and the files grown; were the
/// stream a queue, the subscriber would read `v1` next.
#[test]
fn volatile_publish_appends_nothing_and_a_slow_subscriber_gets_only_the_newest() {
    let root = Scratch::new("signal-exit");
    let socket = root.path().join("sock");
    let log = root.path().join("log");
    let broker = Broker::open(&log).unwrap();
    let mut handle = broker.serve(&socket).unwrap();
    let control = (0u64, "/log/control".to_string(), b"kept".to_vec());

    let mut producer = client(&socket);
    assert!(producer.supports_signals());
    assert_eq!(
        producer.publish(9, 1, "/log/control", b"kept").unwrap(),
        (0, false)
    );
    let before = written(&broker, root.path());

    producer.signal(7, 2, "/s/a", b"v0").unwrap();

    // The subscriber: sent the current value and the mark that closes its first drain,
    // then held there, as a stream blocked on a reader that stopped reading is.
    let (reached_tx, reached) = mpsc::channel();
    let (resume, resume_rx) = mpsc::channel();
    *broker.shared.signal_pause.lock().unwrap() = Some(SignalPause {
        reached: reached_tx,
        resume: resume_rx,
    });
    let mut slow = signals(&socket, "/s/>");
    assert_eq!(
        slow.recv_event().unwrap(),
        Some(SignalEvent::Signal(sig("/s/a", 7, 2, b"v0")))
    );
    assert_eq!(slow.recv_event().unwrap(), Some(SignalEvent::Mark));
    reached.recv_timeout(HANG).unwrap();

    for n in 1..=100u32 {
        producer
            .signal(7, 2, "/s/a", format!("v{n}").as_bytes())
            .unwrap();
    }
    producer.signal(7, 2, "/s/b", b"b1").unwrap();
    producer.signal(7, 2, "/s/b", b"b2").unwrap();
    // The same producer's earlier incarnation, on another connection, arriving late.
    let mut earlier = client(&socket);
    earlier.signal(7, 1, "/s/a", b"an earlier start").unwrap();
    earlier.signal(7, 1, "/s/b", b"an earlier start").unwrap();

    assert_eq!(
        written(&broker, root.path()),
        before,
        "105 signals appended nothing and wrote no file"
    );
    assert_eq!(held(&broker), 2, "one row per subject");
    let mut reader = client(&socket);
    let (records, (_, head)) = reader.fetch(0, "/>", 1000).unwrap();
    assert_eq!(
        (records.as_slice(), head),
        (std::slice::from_ref(&control), 1)
    );
    let (face, _) = reader.last_all("/>").unwrap();
    assert_eq!(
        face,
        std::slice::from_ref(&control),
        "no signal is a subject's last value"
    );

    // Released, the slow subscriber is sent each subject once, at its newest value.
    resume.send(()).unwrap();
    producer.signal(7, 2, "/s/z", b"end").unwrap();
    let mut got = Vec::new();
    loop {
        let next = slow.recv().unwrap().expect("the broker closed the stream");
        if next.subject == "/s/z" {
            assert_eq!(next, sig("/s/z", 7, 2, b"end"));
            break;
        }
        got.push(next);
    }
    assert_eq!(
        got,
        [sig("/s/a", 7, 2, b"v100"), sig("/s/b", 7, 2, b"b2")],
        "a slow subscriber gets only the newest value of each subject"
    );
    assert_eq!(
        written(&broker, root.path()),
        before,
        "delivering them appended nothing either"
    );

    // The broker stops with three signals held; the same log, opened again, holds none.
    drop((slow, producer, earlier, reader));
    handle.shutdown();
    drop(broker);
    let broker = Broker::open(&log).unwrap();
    assert_eq!(broker.head(), 1, "the log holds the control record alone");
    assert_eq!(held(&broker), 0);
    let socket = root.path().join("sock-again");
    let mut handle = broker.serve(&socket).unwrap();
    let mut after = signals(&socket, "/>");
    assert_eq!(
        after.recv_event().unwrap(),
        Some(SignalEvent::Mark),
        "a restarted broker has no signal to send"
    );
    let (records, _) = client(&socket).fetch(0, "/>", 1000).unwrap();
    assert_eq!(records, [control]);
    drop(after);
    handle.shutdown();
}

/// NOTHING OF A SIGNAL OUTLIVES ITS PRODUCER'S SESSION: when the producer's connection
/// ends, the broker drops what that connection still owned, and only that. A subscriber
/// that connects afterwards is sent the other producer's value and no more.
#[test]
fn a_signal_ends_with_its_producers_connection() {
    let root = Scratch::new("signal-session");
    let socket = root.path().join("sock");
    let broker = Broker::open(root.path().join("log")).unwrap();
    let mut handle = broker.serve(&socket).unwrap();

    let mut gone = client(&socket);
    let mut stays = client(&socket);
    gone.signal(1, 1, "/s/gone/cursor", b"here").unwrap();
    gone.signal(1, 1, "/s/shared", b"from the one that goes")
        .unwrap();
    stays.signal(2, 1, "/s/stays/cursor", b"here").unwrap();
    // `stays` takes the shared subject over: it is no longer `gone`'s to lose.
    stays.signal(2, 1, "/s/shared", b"taken over").unwrap();
    assert_eq!(held(&broker), 3);

    let mut watching = signals(&socket, "/s/>");
    assert_eq!(
        first_drain(&mut watching),
        [
            sig("/s/gone/cursor", 1, 1, b"here"),
            sig("/s/stays/cursor", 2, 1, b"here"),
            sig("/s/shared", 2, 1, b"taken over"),
        ]
    );

    drop(gone);
    await_held(&broker, 2);

    // A new subscriber's first drain is what is left, closed by its mark.
    let mut late = signals(&socket, "/s/>");
    assert_eq!(
        first_drain(&mut late),
        [
            sig("/s/stays/cursor", 2, 1, b"here"),
            sig("/s/shared", 2, 1, b"taken over"),
        ]
    );
    // The subscriber that was already there is told nothing of the withdrawal: the next
    // thing it is sent is the next put.
    stays.signal(2, 1, "/s/next", b"n").unwrap();
    assert_eq!(watching.recv().unwrap(), Some(sig("/s/next", 2, 1, b"n")));
    assert_eq!(broker.head(), 0, "and none of it was appended");

    drop((watching, late, stays));
    handle.shutdown();
}

/// ON TCP A SIGNAL HOLDS ITS CONNECTION TO THE KEEPALIVE DEADLINE: a producer that
/// signalled and then says nothing, its socket still open, is ended at the deadline and
/// its value goes with it. NC: without the deadline a peer that vanished with no FIN
/// would leave its value served until the broker restarted.
#[test]
fn a_silent_tcp_producer_is_ended_at_the_keepalive_deadline_and_its_signal_dropped() {
    let root = Scratch::new("signal-tcp");
    let socket = root.path().join("sock");
    let broker = Broker::open(root.path().join("log")).unwrap();
    let mut unix = broker.serve(&socket).unwrap();
    let mut tcp = broker.serve_tcp("127.0.0.1:0").unwrap();
    let addr = tcp.tcp_addr().unwrap().to_string();

    let mut watching = signals(&socket, "/s/>");
    let mut silent = Client::connect_tcp(&addr).unwrap();
    silent.hello().unwrap();
    assert!(silent.supports_signals());
    // Under the default deadline (a minute, the hang detector's own scale) the value is
    // there and is delivered.
    silent.signal(1, 1, "/s/tcp", b"here").unwrap();
    assert_eq!(watching.recv().unwrap(), Some(sig("/s/tcp", 1, 1, b"here")));
    assert_eq!(held(&broker), 1);

    // Each kept signal arms the deadline as it then stands: the next one arms a short one.
    // `silent` then says nothing more, its socket open, and the broker ends it.
    broker.set_keepalive_deadline(Duration::from_millis(20));
    silent.signal(1, 1, "/s/tcp", b"still here").unwrap();
    await_held(&broker, 0);
    let mut local = client(&socket);
    local.signal(2, 1, "/s/z", b"end").unwrap();
    loop {
        let next = watching.recv().unwrap().expect("the broker closed");
        if next.subject == "/s/z" {
            break;
        }
        assert_eq!(next, sig("/s/tcp", 1, 1, b"still here"));
    }

    drop((silent, watching, local));
    tcp.shutdown();
    unix.shutdown();
}

/// TWO PLANES: a log subscription is delivered no signal, and a signal subscription no
/// log record, though both name the same subject. Each stream's next frame after the
/// other plane's write is its OWN plane's next write.
#[test]
fn a_log_subscriber_is_delivered_no_signal_and_a_signal_subscriber_no_record() {
    let root = Scratch::new("signal-planes");
    let socket = root.path().join("sock");
    let broker = Broker::open(root.path().join("log")).unwrap();
    let mut handle = broker.serve(&socket).unwrap();

    let mut log_sub = client(&socket).subscribe(0, "/>").unwrap();
    let mut sig_sub = signals(&socket, "/>");
    let mut producer = client(&socket);
    producer.signal(7, 1, "/both", b"signalled").unwrap();
    assert_eq!(
        producer.publish(7, 1, "/both", b"logged").unwrap(),
        (0, false)
    );
    producer.signal(7, 1, "/both", b"signalled again").unwrap();

    assert_eq!(
        log_sub.recv().unwrap(),
        Some((0, "/both".to_string(), b"logged".to_vec())),
        "the log stream's first delivery is the log record"
    );
    let mut seen = Vec::new();
    while seen.last().map(|s: &Signal| s.body.as_slice()) != Some(&b"signalled again"[..]) {
        seen.push(sig_sub.recv().unwrap().expect("the broker closed"));
    }
    // Conflation may or may not have overtaken the first value; no record is among them.
    for s in &seen {
        assert_eq!((s.subject.as_str(), s.producer_id, s.seq), ("/both", 7, 1));
        assert_ne!(s.body, b"logged");
    }
    assert_eq!(broker.head(), 1);

    drop((log_sub, sig_sub, producer));
    handle.shutdown();
}

/// WHAT IS REFUSED, AND BY WHICH CLASS: a bad subject (2), the broker's own subtree (7),
/// a body past the bound (7), and a connection past its subjects (5). Each refusal keeps
/// the connection and keeps nothing.
#[test]
fn a_bad_or_reserved_subject_an_oversized_body_and_a_full_connection_are_refused() {
    let root = Scratch::new("signal-refused");
    let socket = root.path().join("sock");
    let broker = Broker::open(root.path().join("log")).unwrap();
    let mut handle = broker.serve(&socket).unwrap();
    let mut producer = client(&socket);

    let bad = producer.signal(7, 1, "no-leading-slash", b"").unwrap_err();
    assert_eq!(code(&bad), ERR_BAD_SUBJECT);
    for reserved in ["/a/commit", "/a/anything", "/a"] {
        let refused = producer.signal(7, 1, reserved, b"").unwrap_err();
        assert_eq!(code(&refused), ERR_RECORD_REFUSED, "{reserved}");
    }
    let too_large = vec![0u8; crate::MAX_SIGNAL_BODY + 1];
    let refused = producer.signal(7, 1, "/s/a", &too_large).unwrap_err();
    assert_eq!(code(&refused), ERR_RECORD_REFUSED);
    assert!(broker_refusal(&refused).unwrap().is_permanent());
    assert_eq!(held(&broker), 0, "a refused signal keeps nothing");

    for n in 0..crate::MAX_SIGNAL_SUBJECTS_PER_CONN {
        producer.signal(7, 1, &format!("/s/{n}"), b"").unwrap();
    }
    let full = producer.signal(7, 1, "/s/one-more", b"").unwrap_err();
    assert_eq!(code(&full), ERR_REFUSED);
    // The connection is kept, a subject it holds is still its to replace, and another
    // connection has its own bound.
    producer.signal(7, 1, "/s/0", b"again").unwrap();
    client(&socket).signal(8, 1, "/s/one-more", b"").unwrap();
    assert_eq!(broker.head(), 0);

    drop(producer);
    handle.shutdown();
}

/// A signal is charged to its producer's publish bucket, as a publish is. Every producer's
/// burst here is smaller than the signal's byte charge, so the refusal reads no clock.
#[test]
fn a_signal_past_its_producers_rate_limit_is_refused() {
    let root = Scratch::new("signal-rate");
    let socket = root.path().join("sock");
    let broker = Broker::open(root.path().join("log")).unwrap();
    let mut handle = broker.serve(&socket).unwrap();
    broker
        .set_rate_limit(Some(
            RateLimit::records(1, 1).unwrap().with_bytes(1, 3).unwrap(),
        ))
        .unwrap();
    let mut producer = client(&socket);
    let refused = producer.signal(7, 1, "/s/a", b"body").unwrap_err();
    assert!(broker_refusal(&refused).unwrap().is_rate_limited());
    assert_eq!(held(&broker), 0);
    drop(producer);
    handle.shutdown();
}

/// A BROKER THAT DID NOT OFFER SIGNALS IS SENT NONE: both verbs fail `Unsupported` with no
/// byte written, so the client stays in step. The stand-in broker answers `Hello` with the
/// request set of a build before signals; the next thing it reads is the end of the stream.
#[test]
fn a_client_sends_no_signal_to_a_broker_that_did_not_offer_them() {
    let (ours, theirs) = UnixStream::pair().unwrap();
    let mut theirs = timed(theirs);
    let stand_in = thread::spawn(move || {
        let hello = read_frame(&mut theirs).unwrap().expect("a Hello");
        assert_eq!(decode_request(&hello), Some(Request::Hello));
        let reply = Response::Nonce {
            nonce: vec![0; 32],
            log: Some(crate::LogIdentity {
                id: [7; 16],
                generation: 1,
            }),
            ext: NonceExt {
                requests: Some(REQUEST_SETTLE | REQUEST_FRESH_PUBLISH),
                ..NonceExt::default()
            },
        };
        write_frame(&mut theirs, &encode_response(&reply)).unwrap();
        read_frame(&mut theirs).unwrap()
    });
    let mut client = Client::from_stream(timed(ours));
    client.hello().unwrap();
    assert!(client.supports_fresh_publish());
    assert!(!client.supports_signals());
    let refused = client.signal(7, 1, "/s/a", b"v").unwrap_err();
    assert_eq!(refused.kind(), io::ErrorKind::Unsupported);
    let refused = match client.subscribe_signals("/s/>") {
        Ok(_) => panic!("subscribed to signals nobody offered"),
        Err(e) => e,
    };
    assert_eq!(refused.kind(), io::ErrorKind::Unsupported);
    // The refused subscription dropped the client: the stand-in reads a clean end, with
    // no frame before it.
    assert_eq!(stand_in.join().unwrap(), None);
}

#[cfg(feature = "cap")]
mod guarded {
    use super::*;

    const SECRET: &[u8] = b"signal capability secret";
    const PRINCIPAL: &str = "n-0102030405060708";

    fn mint(grant: &str) -> astream_cap::Capability {
        astream_cap::mint(SECRET, grant).unwrap()
    }

    fn attached(socket: &Path, grant: &str) -> Client {
        let mut client = client(socket);
        let cap = mint(grant);
        client.attach(&cap.filter, &cap.tag).unwrap();
        client
    }

    /// A GUARDED BROKER ADMITS A SIGNAL AS IT ADMITS A PUBLISH: none without a grant,
    /// none outside the grant's filter, none under a read-only grant; and the stream needs
    /// a grant that contains its filter.
    #[test]
    fn a_guarded_broker_admits_a_signal_as_it_admits_a_publish() {
        let root = Scratch::new("signal-cap");
        let socket = root.path().join("sock");
        let broker = Broker::open_guarded(root.path().join("log"), SECRET.to_vec()).unwrap();
        let mut handle = broker.serve(&socket).unwrap();

        let mut writer = attached(&socket, "rw:/s/>");
        writer.signal(7, 1, "/s/a", b"granted").unwrap();
        let outside = writer.signal(7, 1, "/elsewhere", b"x").unwrap_err();
        assert_eq!(code(&outside), ERR_UNAUTHORIZED);
        let mut read_only = attached(&socket, "ro:/s/>");
        let refused = read_only.signal(7, 2, "/s/a", b"read-only").unwrap_err();
        assert_eq!(code(&refused), ERR_UNAUTHORIZED);
        assert_eq!(held(&broker), 1, "a refused signal keeps nothing");

        // The stream: a read grant that contains the filter reads; a narrower one does not.
        assert_eq!(
            first_drain(&mut read_only.subscribe_signals("/s/>").unwrap()),
            [sig("/s/a", 7, 1, b"granted")]
        );
        let mut narrow = attached(&socket, "ro:/s/a")
            .subscribe_signals("/s/>")
            .unwrap();
        assert_eq!(code(&narrow.recv_event().unwrap_err()), ERR_UNAUTHORIZED);
        assert_eq!(broker.head(), 0);

        drop((writer, narrow));
        handle.shutdown();
    }

    /// WHEN THE AUTHORITY LAPSES IS KEPT: on a guarded broker a signal and a signal stream
    /// are each authorized until their grant's own expiry, not for ever, so the value is
    /// kept with that instant (`a_row_past_its_authority_is_not_taken_and_is_removed`
    /// holds the table to it) and the stream ends at it, as a log tail does. The clock is
    /// the argument: no grant here is waited on.
    #[test]
    fn a_signal_and_its_stream_are_authorized_until_their_grants_expiry() {
        let dated = [mint("rw,exp=5000:/s/>")];
        let put = Request::Signal {
            producer_id: 7,
            seq: 1,
            subject: "/s/a".to_string(),
            body: Vec::new(),
        };
        let read = Request::SubscribeSignals {
            filter: "/s/>".to_string(),
        };
        for req in [&put, &read] {
            assert_eq!(cap_authorized_until(SECRET, &dated, req, 4999), Some(5000));
            assert_eq!(cap_authorized_until(SECRET, &dated, req, 5000), None);
            assert_eq!(cap_authorized_until(SECRET, &[], req, 10), None);
        }
        let undated = [mint("rw:/s/>")];
        assert_eq!(
            cap_authorized_until(SECRET, &undated, &put, 10),
            Some(u64::MAX)
        );
        // A principal's grant signals only as that principal's producer.
        let bound = [mint(&format!("rw,p={PRINCIPAL}:/s/>"))];
        let own = astream_cap::producer_id_of(PRINCIPAL);
        let as_producer = |producer_id| Request::Signal {
            producer_id,
            seq: 1,
            subject: "/s/a".to_string(),
            body: Vec::new(),
        };
        assert_eq!(
            cap_authorized_until(SECRET, &bound, &as_producer(own), 10),
            Some(u64::MAX)
        );
        assert_eq!(
            cap_authorized_until(SECRET, &bound, &as_producer(own.wrapping_add(1)), 10),
            None
        );
    }

    /// A REVOCATION TAKES THE VALUE WITH THE AUTHORITY: once the producer's principal is
    /// revoked its signal is served to nobody, though its connection is still open; the
    /// producer's next signal is refused; and a stream whose own grant was that
    /// principal's ends with the refusal. Another producer's value is untouched.
    #[test]
    fn a_revoked_principals_signal_is_dropped_and_its_stream_ended() {
        let root = Scratch::new("signal-revoked");
        let socket = root.path().join("sock");
        let broker = Broker::open_guarded(root.path().join("log"), SECRET.to_vec()).unwrap();
        let mut handle = broker.serve(&socket).unwrap();
        let producer_id = astream_cap::producer_id_of(PRINCIPAL);

        let mut revoked = attached(&socket, &format!("rw,p={PRINCIPAL}:/s/>"));
        revoked.signal(producer_id, 1, "/s/revoked", b"v").unwrap();
        let mut other = attached(&socket, "rw:/s/>");
        other.signal(7, 1, "/s/other", b"v").unwrap();
        let mut its_stream = attached(&socket, &format!("ro,p={PRINCIPAL}:/s/>"))
            .subscribe_signals("/s/>")
            .unwrap();
        assert_eq!(
            first_drain(&mut its_stream),
            [
                sig("/s/revoked", producer_id, 1, b"v"),
                sig("/s/other", 7, 1, b"v"),
            ]
        );

        assert!(broker.revoke_principal(PRINCIPAL));

        // The principal's own stream ends, refused.
        let ended = loop {
            match its_stream.recv_event() {
                Ok(Some(SignalEvent::Mark)) => {}
                Ok(other) => panic!("the revoked stream was sent {other:?}"),
                Err(e) => break e,
            }
        };
        assert_eq!(code(&ended), ERR_UNAUTHORIZED);
        // A reader that comes now is sent the other producer's value alone.
        let mut late = attached(&socket, "ro:/s/>")
            .subscribe_signals("/s/>")
            .unwrap();
        assert_eq!(first_drain(&mut late), [sig("/s/other", 7, 1, b"v")]);
        assert_eq!(held(&broker), 1, "the revoked row is gone, not hidden");
        // And the revoked producer, still connected, cannot put it back.
        let refused = revoked
            .signal(producer_id, 1, "/s/revoked", b"again")
            .unwrap_err();
        assert_eq!(code(&refused), ERR_UNAUTHORIZED);
        assert_eq!(held(&broker), 1);

        drop((revoked, other, late));
        handle.shutdown();
    }
}
