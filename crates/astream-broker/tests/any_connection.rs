//! Evidence for `broker.any-connection-closer`: ONE transport-erased connection —
//! `astream_broker::connect(&Transport, endpoint, connect_timeout)` → `(AnyClient,
//! Closer)` — over every wire this build speaks, with a closer that ends a parked
//! reader from another thread and bounds a request's I/O, and a connect that can be
//! bounded.
//!
//! What the library lacked, and callers (asb, a bridge) each rebuilt on top of it: a
//! closer only for `Subscription<UnixStream>`, read timeouts only per concrete stream
//! type, a TCP connect bounded by nothing but the OS's SYN-retry schedule, and a
//! request/reply with no bound at all — a broker that accepts and never answers
//! parked the caller forever.
//!
//! No sleeps as synchronisation. Every wait ends on a signal (a channel, a delivered
//! record, the kernel reporting the reader asleep) and [`DEADLINE`] is only a hang
//! detector. The one thing measured against the clock is the bound under test itself.
//!
//! Run the whole file with `cargo test -p astream-broker --features handshake --test
//! any_connection` (handshake implies aead); a default build runs the Unix/TCP half
//! plus the feature-off refusals.

use astream_broker::{
    connect, AnyClient, Broker, BrokerHandle, Client, Closer, Subscription, Transport,
};
use std::io::{self, Read, Write};
use std::net::{SocketAddr, TcpListener};
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc;
use std::time::{Duration, Instant};

static CTR: AtomicU64 = AtomicU64::new(0);

/// A HANG DETECTOR, never a synchronisation point: it bounds how long a broken build
/// may take to say so.
const DEADLINE: Duration = Duration::from_secs(30);

/// The timeout under test wherever one is set.
const BOUND: Duration = Duration::from_millis(300);

/// How late past [`BOUND`] a bounded operation may still count as bounded: scheduler
/// noise on a loaded CI box. Below every default it is contrasted with — the sealed
/// handshake's 5 s, the key agreement's 10 s, minutes of SYN retries, and forever for
/// a broker that never answers.
const SLACK: Duration = Duration::from_millis(2500);

/// Distinctive bytes, so a leak in `Debug` cannot hide among zeros.
const KEY: [u8; 32] = [
    0xc3, 0x5a, 0x19, 0xe7, 0x42, 0x8d, 0xb0, 0x6f, 0x13, 0xfe, 0x27, 0x9c, 0x54, 0xa1, 0x08, 0xdb,
    0x7e, 0x31, 0xca, 0x65, 0x9f, 0x02, 0xbd, 0x48, 0xe6, 0x2b, 0x70, 0x1d, 0x8a, 0xf4, 0x36, 0x59,
];

const SUBJ: &str = "/any/conn/x";
const FILTER: &str = "/any/conn/>";

fn fresh(tag: &str, ext: &str) -> PathBuf {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let p = std::env::temp_dir().join(format!("asany_{tag}_{}_{n}.{ext}", std::process::id()));
    let _ = std::fs::remove_file(&p);
    p
}

/// A live broker on a fresh log, reachable as `(transport, endpoint)`.
struct Served {
    _broker: Broker,
    _handle: BrokerHandle,
    transport: Transport,
    endpoint: String,
    files: Vec<PathBuf>,
}

impl Drop for Served {
    fn drop(&mut self) {
        for f in &self.files {
            let _ = std::fs::remove_file(f);
        }
    }
}

fn tcp_served(
    tag: &str,
    transport: Transport,
    serve: impl FnOnce(&Broker) -> BrokerHandle,
) -> Served {
    let log = fresh(tag, "log");
    let broker = Broker::open(&log).unwrap();
    let handle = serve(&broker);
    let endpoint = handle.tcp_addr().expect("a TCP endpoint").to_string();
    Served {
        _broker: broker,
        _handle: handle,
        transport,
        endpoint,
        files: vec![log],
    }
}

#[cfg(unix)]
fn serve_unix(tag: &str) -> Served {
    let log = fresh(tag, "log");
    let sock = fresh(tag, "sock");
    let broker = Broker::open(&log).unwrap();
    let handle = broker.serve(&sock).unwrap();
    Served {
        _broker: broker,
        _handle: handle,
        transport: Transport::Unix,
        endpoint: sock.to_str().unwrap().to_string(),
        files: vec![log, sock],
    }
}

fn serve_tcp(tag: &str) -> Served {
    tcp_served(tag, Transport::Tcp, |b| b.serve_tcp("127.0.0.1:0").unwrap())
}

#[cfg(feature = "aead")]
fn serve_sealed(tag: &str) -> Served {
    tcp_served(tag, Transport::Sealed(Box::new(KEY)), |b| {
        b.serve_tcp_sealed("127.0.0.1:0", KEY).unwrap()
    })
}

#[cfg(feature = "handshake")]
fn serve_handshake(tag: &str) -> Served {
    tcp_served(tag, Transport::Handshake(Box::new(KEY)), |b| {
        b.serve_tcp_handshake("127.0.0.1:0", KEY).unwrap()
    })
}

// ---------------------------------------------------------------------------------
// 1. One erased client round-trips on every transport.
// ---------------------------------------------------------------------------------

/// Publish then fetch through `connect`'s erased client — once with the OS's own
/// connect (`None`, each transport's constructor exactly) and once through the bounded
/// connect path — and read both records back byte-exact on a third connection.
fn round_trip(s: &Served) {
    let (mut a, _closer) = connect(&s.transport, &s.endpoint, None).unwrap();
    assert_eq!(a.publish(7, 1, SUBJ, b"one\x00").unwrap(), (0, false));
    let (mut b, _closer) = connect(&s.transport, &s.endpoint, Some(DEADLINE)).unwrap();
    assert_eq!(b.publish(7, 2, SUBJ, b"two\n").unwrap(), (1, false));
    // Exactly-once still holds through the erased path: a re-send is a dup.
    assert_eq!(b.publish(7, 1, SUBJ, b"one\x00").unwrap(), (0, true));

    let (mut r, _closer) = connect(&s.transport, &s.endpoint, None).unwrap();
    let (page, (next, head)) = r.fetch(0, FILTER, 16).unwrap();
    assert_eq!(
        page,
        vec![
            (0, SUBJ.to_string(), b"one\x00".to_vec()),
            (1, SUBJ.to_string(), b"two\n".to_vec()),
        ],
        "{:?}",
        s.transport
    );
    assert_eq!((next, head), (2, 2));
}

#[cfg(unix)]
#[test]
fn an_erased_client_round_trips_over_unix() {
    round_trip(&serve_unix("rt_unix"));
}

#[test]
fn an_erased_client_round_trips_over_tcp() {
    round_trip(&serve_tcp("rt_tcp"));
}

#[cfg(feature = "aead")]
#[test]
fn an_erased_client_round_trips_over_the_sealed_wire() {
    round_trip(&serve_sealed("rt_sealed"));
}

#[cfg(feature = "handshake")]
#[test]
fn an_erased_client_round_trips_over_the_handshake_wire() {
    round_trip(&serve_handshake("rt_hs"));
}

// ---------------------------------------------------------------------------------
// 2. The closer unparks a thread blocked in `Subscription::recv`, on every transport.
// ---------------------------------------------------------------------------------

/// The calling thread's kernel task id (Linux), so the test can watch the kernel
/// report the reader ASLEEP before it closes — the difference between "the close
/// unparked a blocked read" and "the close happened to land before the read began".
#[cfg(target_os = "linux")]
fn task_id() -> Option<String> {
    let link = std::fs::read_link("/proc/thread-self").ok()?;
    link.file_name()?.to_str().map(str::to_string)
}

#[cfg(not(target_os = "linux"))]
fn task_id() -> Option<String> {
    None
}

/// Wait until the kernel reports task `tid` sleeping (`S` in `/proc/self/task/<tid>/stat`).
/// The task only gets here after its first `recv` returned and it signalled; its next
/// act is the second `recv`, whose socket read is the one thing it can sleep in. Answers
/// false where there is no such `/proc` (then the channel is the only readiness signal,
/// and a close that lands just before the read is seen by that read at once — the same
/// outcome, with the park itself unproven).
fn parked(tid: Option<&str>) -> bool {
    let Some(tid) = tid else { return false };
    let path = format!("/proc/self/task/{tid}/stat");
    let give_up = Instant::now() + DEADLINE;
    while Instant::now() < give_up {
        let Ok(stat) = std::fs::read_to_string(&path) else {
            return false;
        };
        // The state is the first field after the `)` that closes the command name.
        if let Some((_, rest)) = stat.rsplit_once(')') {
            if rest.trim_start().starts_with('S') {
                return true;
            }
        }
        std::thread::yield_now();
    }
    false
}

/// Seed ONE record, subscribe from 0 on the connection under test, and let a reader
/// thread take the seed and then park in the next `recv` (nothing else matches). Then
/// close from THIS thread: the parked `recv` must come back `Ok(None)` — the reader was
/// at a frame boundary — and promptly.
fn close_unparks<S: Read + Write + Send + 'static>(
    what: &str,
    mut sub: Subscription<S>,
    closer: Closer,
) {
    let (ready_tx, ready_rx) = mpsc::channel();
    let (done_tx, done_rx) = mpsc::channel();
    let reader = std::thread::spawn(move || {
        let first = sub.recv().map(|r| r.map(|(_, _, body)| body));
        let _ = ready_tx.send((first, task_id()));
        let _ = done_tx.send(sub.recv());
    });

    let (first, tid) = ready_rx
        .recv_timeout(DEADLINE)
        .unwrap_or_else(|_| panic!("{what}: the seeded record never arrived"));
    assert_eq!(first.unwrap(), Some(b"seed".to_vec()), "{what}");
    let asleep = parked(tid.as_deref());
    if cfg!(target_os = "linux") {
        assert!(asleep, "{what}: the reader never parked in its read");
    }
    // Nothing has come back: the reader is still inside `recv`.
    assert!(
        done_rx.try_recv().is_err(),
        "{what}: recv returned unprompted"
    );

    let t0 = Instant::now();
    closer.close();
    let got = done_rx
        .recv_timeout(DEADLINE)
        .unwrap_or_else(|_| panic!("{what}: close did not unpark the blocked recv"));
    let took = t0.elapsed();
    assert!(
        matches!(got, Ok(None)),
        "{what}: a close at a frame boundary is end-of-stream, got {got:?}"
    );
    assert!(took < SLACK, "{what}: unparking took {took:?}");
    closer.close(); // idempotent: a second close is not an error and does not panic
    reader.join().unwrap();
}

/// The seed, published on a connection of its own.
fn seed(s: &Served) {
    let (mut c, _) = connect(&s.transport, &s.endpoint, None).unwrap();
    c.publish(1, 1, SUBJ, b"seed").unwrap();
}

/// The erased path: the closer came from `connect`, BEFORE `subscribe` consumed the
/// client — the shape a bridge that reconnects needs, since nothing can reach the socket
/// once it is boxed.
fn erased_close_unparks(what: &str, s: &Served) {
    seed(s);
    let (c, closer): (AnyClient, Closer) = connect(&s.transport, &s.endpoint, None).unwrap();
    close_unparks(what, c.subscribe(0, FILTER).unwrap(), closer);
}

#[cfg(unix)]
#[test]
fn the_closer_unparks_a_blocked_recv_over_unix() {
    let s = serve_unix("cl_unix");
    erased_close_unparks("unix (erased)", &s);
    // The concrete path, unchanged for existing callers: `Subscription::closer`.
    let sub = Client::connect(&s.endpoint)
        .unwrap()
        .subscribe(0, FILTER)
        .unwrap();
    let closer = sub.closer().unwrap();
    close_unparks("unix (Subscription::closer)", sub, closer);
}

#[test]
fn the_closer_unparks_a_blocked_recv_over_tcp() {
    let s = serve_tcp("cl_tcp");
    erased_close_unparks("tcp (erased)", &s);
    // `Subscription<TcpStream>::closer` — which did not exist before.
    let sub = Client::connect_tcp(&s.endpoint)
        .unwrap()
        .subscribe(0, FILTER)
        .unwrap();
    let closer = sub.closer().unwrap();
    close_unparks("tcp (Subscription::closer)", sub, closer);
}

#[cfg(feature = "aead")]
#[test]
fn the_closer_unparks_a_blocked_recv_over_the_sealed_wire() {
    let s = serve_sealed("cl_sealed");
    erased_close_unparks("sealed (erased)", &s);
    // `Subscription<SealedStream<TcpStream>>::closer`: a dup of the socket UNDER the
    // record layer, not a second record layer.
    let sub = Client::connect_tcp_sealed(&s.endpoint, KEY)
        .unwrap()
        .subscribe(0, FILTER)
        .unwrap();
    let closer = sub.closer().unwrap();
    close_unparks("sealed (Subscription::closer)", sub, closer);
}

#[cfg(feature = "handshake")]
#[test]
fn the_closer_unparks_a_blocked_recv_over_the_handshake_wire() {
    let s = serve_handshake("cl_hs");
    erased_close_unparks("handshake (erased)", &s);
    let sub = Client::connect_tcp_handshake(&s.endpoint, KEY)
        .unwrap()
        .subscribe(0, FILTER)
        .unwrap();
    let closer = sub.closer().unwrap();
    close_unparks("handshake (Subscription::closer)", sub, closer);
}

// ---------------------------------------------------------------------------------
// 3. The closer bounds a request to a broker that accepts and never answers.
// ---------------------------------------------------------------------------------

/// A fake broker: accept ONE connection and hand the accepted socket back — held open,
/// never read, never written. The accept is awaited before the request is made, so the
/// silence is a peer's, not a missing listener's.
fn silent_peer<L, S>(listener: L, accept: fn(&L) -> io::Result<S>) -> mpsc::Receiver<S>
where
    L: Send + 'static,
    S: Send + 'static,
{
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        if let Ok(s) = accept(&listener) {
            let _ = tx.send(s);
        }
    });
    rx
}

fn is_timeout(e: &io::Error) -> bool {
    matches!(
        e.kind(),
        io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut
    )
}

/// `set_read_timeout` turns "parked forever" into a timeout error within the bound.
fn read_bound_holds<S>(what: &str, transport: &Transport, endpoint: &str, peer: mpsc::Receiver<S>) {
    let (mut c, closer) = connect(transport, endpoint, None).unwrap();
    let _held = peer
        .recv_timeout(DEADLINE)
        .unwrap_or_else(|_| panic!("{what}: the fake broker never accepted"));
    closer.set_read_timeout(Some(BOUND)).unwrap();
    let t0 = Instant::now();
    let err = match c.publish(1, 1, SUBJ, b"x") {
        Ok(ack) => panic!("{what}: a silent peer acked {ack:?}"),
        Err(e) => e,
    };
    let took = t0.elapsed();
    assert!(is_timeout(&err), "{what}: expected a timeout, got {err:?}");
    assert!(
        took < BOUND + SLACK,
        "{what}: the bounded request took {took:?}"
    );
}

/// `set_write_timeout` bounds a request the peer never READS: pipelined 1 MiB publishes
/// fill both socket buffers, and the write that finds them full fails within the bound
/// instead of parking. (A 1 MiB body is under the frame cap, so the refusal is the
/// socket's, not the codec's.)
fn write_bound_holds<S>(
    what: &str,
    transport: &Transport,
    endpoint: &str,
    peer: mpsc::Receiver<S>,
) {
    let (mut c, closer) = connect(transport, endpoint, None).unwrap();
    let _held = peer
        .recv_timeout(DEADLINE)
        .unwrap_or_else(|_| panic!("{what}: the fake broker never accepted"));
    closer.set_write_timeout(Some(BOUND)).unwrap();
    let body = vec![0x5au8; 1 << 20];
    let t0 = Instant::now();
    let mut sent = 0u64;
    let err = loop {
        match c.send_publish(1, sent + 1, SUBJ, &body) {
            Ok(()) => sent += 1,
            Err(e) => break e,
        }
        assert!(
            sent < 1024,
            "{what}: 1 GiB went into a peer that never reads"
        );
    };
    let took = t0.elapsed();
    assert!(is_timeout(&err), "{what}: expected a timeout, got {err:?}");
    assert!(
        took < BOUND + SLACK,
        "{what}: the bounded write took {took:?}"
    );
}

#[test]
fn the_closer_bounds_a_request_to_a_tcp_peer_that_never_answers() {
    let l = TcpListener::bind("127.0.0.1:0").unwrap();
    let ep = l.local_addr().unwrap().to_string();
    let peer = silent_peer(l, |l| l.accept().map(|(s, _)| s));
    read_bound_holds("tcp read", &Transport::Tcp, &ep, peer);

    let l = TcpListener::bind("127.0.0.1:0").unwrap();
    let ep = l.local_addr().unwrap().to_string();
    let peer = silent_peer(l, |l| l.accept().map(|(s, _)| s));
    write_bound_holds("tcp write", &Transport::Tcp, &ep, peer);
}

#[cfg(unix)]
#[test]
fn the_closer_bounds_a_request_to_a_unix_peer_that_never_answers() {
    use std::os::unix::net::UnixListener;
    for write in [false, true] {
        let path = fresh("silent", "sock");
        let l = UnixListener::bind(&path).unwrap();
        let ep = path.to_str().unwrap().to_string();
        let peer = silent_peer(l, |l| l.accept().map(|(s, _)| s));
        if write {
            write_bound_holds("unix write", &Transport::Unix, &ep, peer);
        } else {
            read_bound_holds("unix read", &Transport::Unix, &ep, peer);
        }
        let _ = std::fs::remove_file(&path);
    }
}

/// On the sealed wires the connect itself is the first request: a peer that accepts and
/// never answers the hello fails the CONNECT, and a `connect_timeout` replaces the
/// built-in handshake deadline (5 s sealed, 10 s key agreement) — so it fails within
/// the caller's bound, well inside either default.
#[cfg(feature = "aead")]
fn a_silent_peer_fails_the_bounded_handshake(what: &str, transport: &Transport) {
    let l = TcpListener::bind("127.0.0.1:0").unwrap();
    let ep = l.local_addr().unwrap().to_string();
    let _peer = silent_peer(l, |l| l.accept().map(|(s, _)| s));
    let t0 = Instant::now();
    let err = match connect(transport, &ep, Some(BOUND)) {
        Ok(_) => panic!("{what}: a silent peer completed the handshake"),
        Err(e) => e,
    };
    let took = t0.elapsed();
    assert!(is_timeout(&err), "{what}: expected a timeout, got {err:?}");
    assert!(
        took < BOUND + SLACK,
        "{what}: the bounded handshake took {took:?}"
    );
}

#[cfg(feature = "aead")]
#[test]
fn a_connect_timeout_bounds_the_sealed_handshake() {
    a_silent_peer_fails_the_bounded_handshake("sealed", &Transport::Sealed(Box::new(KEY)));
}

#[cfg(feature = "handshake")]
#[test]
fn a_connect_timeout_bounds_the_key_agreement() {
    a_silent_peer_fails_the_bounded_handshake("handshake", &Transport::Handshake(Box::new(KEY)));
}

// ---------------------------------------------------------------------------------
// 4. The connect timeout.
// ---------------------------------------------------------------------------------

/// A connect to an address that never answers fails within the bound, where an
/// unbounded connect would wait out the kernel's SYN retries (minutes).
///
/// THE BLACK HOLE is a listener that never accepts, with its accept queue filled: Linux
/// then DROPS further SYNs (under the default `net.ipv4.tcp_abort_on_overflow = 0`) —
/// no RST, no answer, exactly what a firewalled or dead host looks like to the client.
/// A non-routable address is NOT used, because what one does depends on the host's
/// routing (on the machine this was written on, 192.0.2.1 is refused at once while
/// 10.255.255.1 is silent), so it would prove the bound on one box and nothing on the
/// next. Linux only: other kernels size and police the accept queue differently, and
/// what this test does not prove there it does not claim.
#[cfg(target_os = "linux")]
#[test]
fn a_connect_timeout_bounds_a_connect_the_peer_never_answers() {
    // Only this Linux-only test names the raw stream; a file-level import is unused on
    // every other host and trips `-D unused-imports` there.
    use std::net::TcpStream;
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let addr = listener.local_addr().unwrap();
    // Fill the queue with raw connects (one descriptor each): every one completes in
    // the kernel until the queue is full, and the first that does not is the signal
    // that it is. Bounded, so a kernel that never drops SYNs fails loudly here.
    let mut held: Vec<TcpStream> = Vec::new();
    loop {
        match TcpStream::connect_timeout(&addr, BOUND) {
            Ok(s) => held.push(s),
            Err(e) if e.kind() == io::ErrorKind::TimedOut => break,
            Err(e) => panic!(
                "filling the accept queue after {} connects: {e}",
                held.len()
            ),
        }
        assert!(
            held.len() < 8192,
            "the accept queue never filled: this kernel does not drop SYNs to a full listener"
        );
    }

    // The queue is full and nothing accepts: the connect under test gets silence.
    let t0 = Instant::now();
    let err = match connect(&Transport::Tcp, &addr.to_string(), Some(BOUND)) {
        Ok(_) => panic!("connected to a listener whose accept queue is full"),
        Err(e) => e,
    };
    let took = t0.elapsed();
    assert_eq!(err.kind(), io::ErrorKind::TimedOut, "{err:?}");
    assert!(
        took >= BOUND,
        "failed after {took:?}, before the bound: not the timeout"
    );
    assert!(took < BOUND + SLACK, "the bounded connect took {took:?}");
    drop(listener);
}

/// Every resolved address is tried in turn: a refused first address does not fail the
/// connect while a later one answers.
#[test]
fn a_bounded_connect_tries_each_resolved_address() {
    let s = serve_tcp("each");
    let live: SocketAddr = s.endpoint.parse().unwrap();
    let dead = {
        let l = TcpListener::bind("127.0.0.1:0").unwrap();
        l.local_addr().unwrap()
    }; // dropped: nothing listens there now

    let refused = match Client::connect_tcp_timeout(&[dead][..], DEADLINE) {
        Ok(_) => panic!("{dead} was supposed to be dead"),
        Err(e) => e,
    };
    assert_eq!(
        refused.kind(),
        io::ErrorKind::ConnectionRefused,
        "{refused:?}"
    );

    let mut c = Client::connect_tcp_timeout(&[dead, live][..], DEADLINE).unwrap();
    assert_eq!(
        c.publish(3, 1, SUBJ, b"second address").unwrap(),
        (0, false)
    );
}

/// A zero timeout is refused up front, on every transport alike — std would refuse it
/// for TCP, but a Unix connect would otherwise ignore it silently.
#[test]
fn a_zero_connect_timeout_is_refused_on_every_transport() {
    for t in [
        Transport::Unix,
        Transport::Tcp,
        Transport::Sealed(Box::new(KEY)),
        Transport::Handshake(Box::new(KEY)),
    ] {
        match connect(&t, "127.0.0.1:1", Some(Duration::ZERO)) {
            Ok(_) => panic!("{t:?}: a zero connect timeout was accepted"),
            Err(e) => assert_eq!(e.kind(), io::ErrorKind::InvalidInput, "{t:?}: {e:?}"),
        }
    }
}

// ---------------------------------------------------------------------------------
// 5. Debug never prints the key; a missing feature is refused by name.
// ---------------------------------------------------------------------------------

#[test]
fn transport_debug_never_prints_the_key() {
    let lower: String = KEY.iter().map(|b| format!("{b:02x}")).collect();
    let upper = lower.to_uppercase();
    let as_array = format!("{KEY:?}");
    for (t, want) in [
        (Transport::Sealed(Box::new(KEY)), "Sealed(<key redacted>)"),
        (
            Transport::Handshake(Box::new(KEY)),
            "Handshake(<key redacted>)",
        ),
    ] {
        // Exactly the variant and the word "redacted" — in the plain, the pretty and a
        // cloned value's rendering — so no spelling of the key (hex either case, the
        // decimal array `[u8; 32]`'s own Debug prints) can be in it.
        for shown in [
            format!("{t:?}"),
            format!("{t:#?}"),
            format!("{:?}", t.clone()),
        ] {
            assert_eq!(shown, want);
            assert!(
                !shown.contains(&lower) && !shown.contains(&upper),
                "{shown}"
            );
            assert!(!shown.contains(&as_array), "{shown}");
        }
    }
    assert_eq!(format!("{:?}", Transport::Tcp), "Tcp");
    assert_eq!(format!("{:?}", Transport::Unix), "Unix");
}

/// Without `aead` the sealed variant still exists (so an exhaustive match compiles in
/// every build) and `connect` refuses it by NAME — before dialing anything, so it can
/// never become a plaintext connection.
#[cfg(not(feature = "aead"))]
#[test]
fn the_sealed_wire_is_refused_by_name_without_aead() {
    match connect(&Transport::Sealed(Box::new(KEY)), "127.0.0.1:1", None) {
        Ok(_) => panic!("a sealed connect without the aead feature"),
        Err(e) => {
            assert_eq!(e.kind(), io::ErrorKind::Unsupported, "{e:?}");
            assert!(e.to_string().contains("`aead`"), "{e}");
        }
    }
}

#[cfg(not(feature = "handshake"))]
#[test]
fn the_handshake_wire_is_refused_by_name_without_handshake() {
    match connect(&Transport::Handshake(Box::new(KEY)), "127.0.0.1:1", None) {
        Ok(_) => panic!("a handshake connect without the handshake feature"),
        Err(e) => {
            assert_eq!(e.kind(), io::ErrorKind::Unsupported, "{e:?}");
            assert!(e.to_string().contains("`handshake`"), "{e}");
        }
    }
}
