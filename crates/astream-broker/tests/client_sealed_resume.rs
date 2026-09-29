//! Regression: a mid-frame timeout under the SEALED transport resumes on both layers.
//!
//! With `set_read_timeout` now settable on a sealed subscription, the timeout sits on
//! the `TcpStream` UNDERNEATH the AEAD record layer, so it can land in the middle of a
//! sealed record AND in the middle of a Frame. The record layer already keeps its
//! partial record and its sequence counter across one (`astream_aead::read_record`);
//! this pins the other half — the Frame layer keeps the plaintext prefix it had
//! already been handed, instead of dropping it and reading a body as the next header.
//!
//! Run with `cargo test -p astream-broker --features aead --test client_sealed_resume`.
//!
//! No sleeps: the timeout is injected by a wrapper socket at an exact byte offset,
//! which is the observable shape of `SO_RCVTIMEO`. The real timeout on the socket is a
//! generous HANG DETECTOR only — every take below asks for exactly one record, so a
//! healthy run never waits on it.
#![cfg(feature = "aead")]

use astream_aead::SealedStream;
use astream_broker::client::take;
use astream_broker::{Broker, BrokerHandle, Client};
use std::io::{self, Read, Write};
use std::net::TcpStream;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

static CTR: AtomicU64 = AtomicU64::new(0);

const KEY: [u8; 32] = [
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff, 0x00,
    0x0f, 0x1e, 0x2d, 0x3c, 0x4b, 0x5a, 0x69, 0x78, 0x87, 0x96, 0xa5, 0xb4, 0xc3, 0xd2, 0xe1, 0xf0,
];

const LANE: &str = "/f/F/in/p/h-andrew/>";
const SUBJ: &str = "/f/F/in/p/h-andrew/screen";
const GROUP: &str = "/f/F/cur/p/h-andrew/inbox";

/// A record too big for one sealed record, let alone one read.
const BIG: usize = 200 * 1024;

/// Sealed bytes to deliver after arming before the injected timeout: several whole
/// sealed records' worth, so the record layer has already handed the Frame layer a
/// large plaintext prefix, and the frame is still far from complete.
const CUT_AT: usize = 150_000;

/// The hang detector on the socket. Not a synchronisation point: nothing below waits
/// for it on a healthy run.
const HANG: Duration = Duration::from_secs(20);

/// Rounds the resume loop may burn before declaring a hang.
const MAX_ROUNDS: usize = 3;

#[derive(Default)]
struct Cut {
    armed: bool,
    fired: bool,
    delivered: usize,
}

/// A socket that times out ONCE, `CUT_AT` bytes after it is armed — the mid-record
/// timeout `SO_RCVTIMEO` produces under a sealed stream while a large record is still
/// arriving. Armed after the handshake so the handshake's own reads are not counted.
struct Choppy {
    inner: TcpStream,
    cut: Arc<Mutex<Cut>>,
}

impl Read for Choppy {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let room = {
            let mut c = self.cut.lock().unwrap();
            if !c.armed || c.fired {
                None
            } else if c.delivered >= CUT_AT {
                c.fired = true;
                return Err(io::Error::new(io::ErrorKind::TimedOut, "injected timeout"));
            } else {
                Some((CUT_AT - c.delivered).min(buf.len()))
            }
        };
        match room {
            None => self.inner.read(buf),
            Some(room) => {
                let n = self.inner.read(&mut buf[..room])?;
                self.cut.lock().unwrap().delivered += n;
                Ok(n)
            }
        }
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

/// Removes its paths when dropped, each with every `<path>.*` sidecar beside it (the
/// broker's `.hw`, `.base`, `.replica`, …), so a test leaves nothing behind whether it
/// passes or panics. Bind it before whatever uses the paths, so it drops after that.
struct Cleanup(Vec<PathBuf>);

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

fn sealed_broker(tag: &str) -> (Cleanup, Broker, BrokerHandle, String) {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = std::env::temp_dir().join(format!("asr2sres_{tag}_{pid}_{n}.log"));
    let _ = std::fs::remove_file(&log);
    let tmp = Cleanup::new(&[&log]);
    let broker = Broker::open(&log).unwrap();
    let h = broker.serve_tcp_sealed("127.0.0.1:0", KEY).unwrap();
    let addr = h.tcp_addr().expect("a TCP endpoint").to_string();
    (tmp, broker, h, addr)
}

#[test]
fn a_mid_record_timeout_under_the_seal_resumes_the_frame() {
    let (_tmp, _b, _h, addr) = sealed_broker("resume");

    let body = vec![0xFFu8; BIG];
    let mut prod = Client::connect_tcp_sealed(&addr, KEY).unwrap();
    assert_eq!(prod.publish(1, 1, SUBJ, &body).unwrap(), (0, false));

    let tcp = TcpStream::connect(&addr).unwrap();
    tcp.set_nodelay(true).unwrap();
    tcp.set_read_timeout(Some(HANG)).unwrap();
    let cut = Arc::new(Mutex::new(Cut::default()));
    let sealed = SealedStream::handshake_client(
        Choppy {
            inner: tcp,
            cut: Arc::clone(&cut),
        },
        KEY,
    )
    .unwrap();
    let mut sub = Client::from_stream(sealed)
        .subscribe_group(GROUP, LANE)
        .unwrap();
    // Arm now: the handshake's reads are behind us, so the count starts at the first
    // byte of the delivery.
    cut.lock().unwrap().armed = true;

    // The timeout lands deep inside the only record: nothing COMPLETE to return.
    assert!(
        take(&mut sub, 1).unwrap().is_empty(),
        "a take cut off inside the frame has no complete record"
    );
    assert!(
        cut.lock().unwrap().fired,
        "the timeout was actually injected"
    );

    // The plaintext prefix that timeout had already been handed is still owed to the
    // caller. Before the fix this read the body as a frame header and errored.
    let mut got = Vec::new();
    let mut rounds = 0;
    while got.is_empty() {
        got.extend(take(&mut sub, 1).unwrap());
        rounds += 1;
        assert!(rounds < MAX_ROUNDS, "the resumed record never arrived");
    }
    assert_eq!(got[0].0, 0);
    assert_eq!(got[0].1, SUBJ);
    assert_eq!(got[0].2, body, "the whole body, not a suffix of it");
}
