//! Regression: an idle stop in `client::take` / `client::drain` is FRAME-ATOMIC.
//!
//! `Subscription::set_read_timeout` puts the timeout on the SOCKET, so it can land
//! part-way through a record — after the 8-byte frame header, or in the middle of a
//! body. `read_frame` is built out of `read_exact`, which returns the timeout having
//! already consumed whatever bytes arrived, into a buffer it drops. Before the fix
//! `take` reported that as a clean "idle: nothing more right now" while a prefix of a
//! record had been eaten off the stream, so the NEXT read on the same subscription
//! parsed the tail of that body as a frame header: `InvalidData: corrupt frame` at
//! best, a fabricated record at worst. Re-using one subscription across drains is the
//! documented shape (tests/inbox_drain.rs), so this was reachable on the ordinary path
//! as soon as a record was big enough to be delivered in more than one read.
//!
//! No sleeps: the mid-frame timeout is injected by a wrapper stream at an exact byte
//! offset, which is the observable shape of `SO_RCVTIMEO` (the reads before the
//! deadline hand back the bytes that arrived; the read that spans it returns
//! `TimedOut`). The socket underneath carries a real, generous read timeout as a HANG
//! DETECTOR — never as a synchronisation point: every assertion below is a loop that
//! keeps draining until the records are in hand, so a slow machine takes another
//! round rather than failing.
#![cfg(unix)]

use astream_broker::client::{drain, take};
use astream_broker::{Broker, BrokerHandle, Client};
use std::io::{self, Read, Write};
use std::os::unix::net::UnixStream;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

static CTR: AtomicU64 = AtomicU64::new(0);

const LANE: &str = "/f/F/in/n1/s1/>";
const SUBJ: &str = "/f/F/in/n1/s1/snap";
const GROUP: &str = "/f/F/cur/n1/node/inbox";

/// The idle window. It bounds reads that are expected to find nothing, and it bounds
/// nothing else — the loops below re-drain rather than assert on one window.
const IDLE: Duration = Duration::from_millis(250);

/// How many idle windows a loop may burn before it is declared hung. Generous on
/// purpose (this is ~50s, not a performance assertion); the happy path takes two.
const MAX_ROUNDS: usize = 200;

/// A record big enough that the broker cannot hand it over in one read.
const BIG: usize = 200 * 1024;

/// Bytes of the first frame to deliver before the injected timeout: the 8-byte header
/// plus 64 bytes of payload, which is past the `Delivery` response's offset/subject
/// prefix and inside the body. Before the fix those 64 bytes were dropped and the
/// body's next 8 bytes were read as the following frame's header.
const CUT: usize = 8 + 64;

struct Paths {
    sock: String,
    log: String,
}

fn fresh(tag: &str) -> Paths {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let p = Paths {
        sock: format!("/tmp/asr2idle_{tag}_{pid}_{n}.sock"),
        log: format!("/tmp/asr2idle_{tag}_{pid}_{n}.log"),
    };
    let _ = std::fs::remove_file(&p.sock);
    let _ = std::fs::remove_file(&p.log);
    p
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

fn serve(p: &Paths) -> (Broker, BrokerHandle) {
    let broker = Broker::open(&p.log).unwrap();
    let handle = broker.serve(&p.sock).unwrap();
    (broker, handle)
}

/// A socket that times out ONCE, `cut` bytes into the stream — the mid-frame timeout
/// a real `SO_RCVTIMEO` produces when a large record is still arriving. Every read
/// before the cut hands back the bytes that have arrived; the read at the cut returns
/// `TimedOut` and the wrapper then gets out of the way.
struct Choppy {
    inner: UnixStream,
    delivered: usize,
    cut: Option<usize>,
}

impl Read for Choppy {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if let Some(cut) = self.cut {
            if self.delivered >= cut {
                self.cut = None;
                return Err(io::Error::new(io::ErrorKind::TimedOut, "injected timeout"));
            }
            let room = (cut - self.delivered).min(buf.len());
            let n = self.inner.read(&mut buf[..room])?;
            self.delivered += n;
            return Ok(n);
        }
        self.inner.read(buf)
    }
}

impl Write for Choppy {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.inner.write(buf)
    }
    fn flush(&mut self) -> io::Result<()> {
        self.inner.flush()
    }
}

/// A group subscription whose socket times out once, mid-frame, at `CUT`.
fn cut_sub(sock: &str) -> astream_broker::Subscription<Choppy> {
    let inner = UnixStream::connect(sock).unwrap();
    // A real timeout on the socket: the HANG DETECTOR for reads that find nothing.
    inner.set_read_timeout(Some(IDLE)).unwrap();
    Client::from_stream(Choppy {
        inner,
        delivered: 0,
        cut: Some(CUT),
    })
    .subscribe_group(GROUP, LANE)
    .unwrap()
}

/// A timeout that lands in the middle of a record does not eat it: the subscription
/// keeps the partial frame and the next take returns the SAME record, whole.
#[test]
fn a_mid_frame_timeout_resumes_the_record_instead_of_desynchronising() {
    let p = fresh("resume");
    let (_b, _h) = serve(&p);

    let body = vec![0xFFu8; BIG];
    let mut prod = Client::connect(&p.sock).unwrap();
    assert_eq!(prod.publish(1, 1, SUBJ, &body).unwrap(), (0, false));

    let mut sub = cut_sub(&p.sock);

    // The timeout lands 64 payload bytes into the only record, so nothing complete
    // has arrived: an idle stop with an empty answer, as documented.
    assert!(
        take(&mut sub, 8).unwrap().is_empty(),
        "a take cut off inside the first frame has no COMPLETE record to return"
    );

    // The bytes eaten by that timeout are still owed to the caller. Before the fix
    // this take read the body as a frame header and returned an error.
    let mut got = Vec::new();
    let mut rounds = 0;
    while got.is_empty() {
        got.extend(take(&mut sub, 8).unwrap());
        rounds += 1;
        assert!(rounds < MAX_ROUNDS, "the resumed record never arrived");
    }
    assert_eq!(got.len(), 1, "one record was published, one is delivered");
    assert_eq!(got[0].0, 0);
    assert_eq!(got[0].1, SUBJ);
    assert_eq!(got[0].2, body, "the whole body, not a suffix of it");

    // And the stream is at a frame boundary again: nothing left over.
    assert!(take(&mut sub, 8).unwrap().is_empty());
}

/// The same cut on the documented `drain` shape: re-using ONE subscription across
/// drains still delivers every record exactly once, and the group's commit follows.
#[test]
fn drain_across_a_mid_frame_timeout_is_still_exactly_once() {
    let p = fresh("drain");
    let (_b, _h) = serve(&p);

    let big = vec![0xFFu8; BIG];
    let mut prod = Client::connect(&p.sock).unwrap();
    prod.publish(1, 1, SUBJ, &big).unwrap();
    prod.publish(1, 2, SUBJ, b"second").unwrap();

    let mut sub = cut_sub(&p.sock);
    let mut committer = Client::connect(&p.sock).unwrap();

    let mut got: Vec<(u64, String, Vec<u8>)> = Vec::new();
    let mut rounds = 0;
    while got.len() < 2 {
        got.extend(drain(&mut sub, &mut committer, GROUP, 8).unwrap());
        rounds += 1;
        assert!(rounds < MAX_ROUNDS, "the drain never caught up");
    }
    assert_eq!(got.len(), 2, "two published, two delivered — no duplicate");
    assert_eq!((got[0].0, got[1].0), (0, 1));
    assert_eq!(got[0].2, big);
    assert_eq!(got[1].2, b"second".to_vec());

    // The commit landed: a fresh group subscription is handed nothing.
    let mut again = Client::connect(&p.sock)
        .unwrap()
        .subscribe_group(GROUP, LANE)
        .unwrap();
    again.set_read_timeout(Some(IDLE)).unwrap();
    assert!(
        take(&mut again, 8).unwrap().is_empty(),
        "the group is committed through the last record"
    );
}
