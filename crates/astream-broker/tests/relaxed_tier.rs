//! Evidence for `broker.relaxed-tier`: the Relaxed point on the durability dial. An
//! `ack` means the batch is in the OS page cache (NO fsync) — lower latency / higher
//! throughput, the honest trade being it survives a PROCESS crash but not a power loss.
//! What we CAN prove deterministically is that it stays crash-CONSISTENT and
//! exactly-once: acked records are delivered, a re-send is deduped, and after a broker
//! restart the log recovers a clean in-order prefix (no corruption, no gaps). We do NOT
//! claim power-loss durability for Relaxed (that is exactly what Strict is for).

#![cfg(unix)] // serves the broker on a Unix-domain socket; std has no UDS on Windows

use astream_broker::{Broker, Client, Durability};
use std::sync::atomic::{AtomicU64, Ordering};

static CTR: AtomicU64 = AtomicU64::new(0);

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

#[test]
fn relaxed_tier_is_crash_consistent_ordered_and_exactly_once() {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = format!("/tmp/asrelaxed_{pid}_{n}.log");
    let sock1 = format!("/tmp/asrelaxed_{pid}_a_{n}.sock");
    let sock2 = format!("/tmp/asrelaxed_{pid}_b_{n}.sock");
    let _ = std::fs::remove_file(&log);
    let _tmp = Cleanup::new(&[&log, &sock1, &sock2]);

    const N: u64 = 200;

    {
        let b = Broker::open_with(&log, Durability::Relaxed).unwrap();
        let mut h = b.serve(&sock1).unwrap();
        let mut p = Client::connect(&sock1).unwrap();
        for i in 1..=N {
            let (off, deduped) = p
                .publish(1, i, "/a/rx/x", format!("m{i}").as_bytes())
                .unwrap();
            assert_eq!(
                (off, deduped),
                (i - 1, false),
                "Relaxed acks assign a dense spine"
            );
        }
        // Re-send (1,1): exactly-once ingest holds at the Relaxed tier too.
        assert_eq!(
            p.publish(1, 1, "/a/rx/x", b"dup").unwrap(),
            (0, true),
            "Relaxed dedup returns the original offset"
        );
        // Delivery works: a subscriber from 0 sees all N in order.
        let mut sub = Client::connect(&sock1)
            .unwrap()
            .subscribe(0, "/a/rx/>")
            .unwrap();
        for i in 0..N {
            let (off, _s, _b) = sub.recv().unwrap().unwrap();
            assert_eq!(off, i, "delivered in order");
        }
        h.shutdown();
    }

    // Restart (recovery is tier-independent — both keep the longest intact prefix). The
    // page-cache writes survived the graceful shutdown, so all N records recover cleanly.
    let b2 = Broker::open_with(&log, Durability::Relaxed).unwrap();
    let _h2 = b2.serve(&sock2).unwrap();
    let mut sub = Client::connect(&sock2)
        .unwrap()
        .subscribe(0, "/a/rx/>")
        .unwrap();
    for i in 0..N {
        let (off, _s, _b) = sub.recv().unwrap().unwrap();
        assert_eq!(
            off, i,
            "all {N} recovered in order after restart (crash-consistent)"
        );
    }
    // dedup survived the restart.
    assert_eq!(
        Client::connect(&sock2)
            .unwrap()
            .publish(1, 1, "/a/rx/x", b"dup")
            .unwrap(),
        (0, true),
        "exactly-once ingest survived the Relaxed restart"
    );
}

/// The child half of `relaxed_acked_records_survive_a_real_sigkill_of_the_broker`: this
/// test binary re-executes itself running ONLY this function (`relaxed_child --exact`)
/// with `ASTREAM_RELAXED_CHILD=<log>|<sock>` set. It serves a RELAXED broker on `<sock>`
/// over `<log>`, prints `listening` once the socket is up, and blocks until it is
/// SIGKILLed — no shutdown, no flush, no fsync ever runs. In a normal `cargo test` run
/// (no env var) it does nothing.
#[test]
fn relaxed_child() {
    let Ok(spec) = std::env::var("ASTREAM_RELAXED_CHILD") else {
        return;
    };
    let (log, sock) = spec.split_once('|').expect("<log>|<sock>");
    let b = Broker::open_with(log, Durability::Relaxed).expect("child: open");
    let _h = b.serve(sock).expect("child: serve");
    println!("listening");
    loop {
        std::thread::sleep(std::time::Duration::from_secs(3600));
    }
}

/// The sentence "survives a PROCESS crash (kill -9)" witnessed for real: a Relaxed
/// broker in a CHILD PROCESS acks N publishes (page-cache writes, never fsync'd), is
/// SIGKILLed with no shutdown path of any kind, and this process reopens the log —
/// every acked record is recovered in order and the dedup map is intact. Then a torn
/// tail (a frame cut mid-write, the state a kill mid-append leaves) is appended and the
/// reopen truncates exactly it: Relaxed is crash-CONSISTENT (no corruption, no gaps),
/// it merely does not promise power-loss durability. Synchronizes on the child's
/// `listening` line and on `wait()` after the kill — no sleeps.
#[test]
fn relaxed_acked_records_survive_a_real_sigkill_of_the_broker() {
    use std::io::{BufRead, BufReader, Write};
    use std::process::{Command, Stdio};

    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = format!("/tmp/asrelaxed_kill_{pid}_{n}.log");
    let sock = format!("/tmp/asrelaxed_kill_{pid}_{n}.sock");
    let sock2 = format!("/tmp/asrelaxed_kill2_{pid}_{n}.sock");
    let _ = std::fs::remove_file(&log);
    let _ = std::fs::remove_file(&sock);
    let _tmp = Cleanup::new(&[&log, &sock, &sock2]);
    const N: u64 = 100;

    let mut child = Command::new(std::env::current_exe().unwrap())
        .args(["relaxed_child", "--exact", "--nocapture"])
        .env("ASTREAM_RELAXED_CHILD", format!("{log}|{sock}"))
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("spawn the child broker");
    {
        // Sync on data: the child prints `listening` once the socket is bound.
        let mut lines = BufReader::new(child.stdout.take().unwrap()).lines();
        loop {
            match lines.next() {
                Some(Ok(l)) if l.trim() == "listening" => break,
                Some(Ok(_)) => continue, // the harness's own "running 1 test" line
                other => panic!("child broker did not come up: {other:?}"),
            }
        }
    }

    let mut p = Client::connect(&sock).unwrap();
    for i in 1..=N {
        assert_eq!(
            p.publish(1, i, "/a/rx/x", format!("m{i}").as_bytes())
                .unwrap(),
            (i - 1, false)
        );
    }
    // SIGKILL: the child never shuts down, flushes, or fsyncs. The acked bytes are in
    // the kernel's page cache only.
    child.kill().expect("SIGKILL the child broker");
    let _ = child.wait();
    drop(p);
    let _ = std::fs::remove_file(&sock);

    // A torn tail on top: the first 20 bytes of a would-be record N (a kill mid-write).
    let torn = astream_broker::BrokerRecord {
        seq: astream_wire::Offset(N),
        producer_id: 1,
        producer_seq: N + 1,
        subject: "/a/rx/x".to_string(),
        body: b"interrupted".to_vec(),
        commit: None,
    }
    .encode()
    .unwrap();
    let clean_len = std::fs::metadata(&log).unwrap().len();
    std::fs::OpenOptions::new()
        .append(true)
        .open(&log)
        .unwrap()
        .write_all(&torn[..20])
        .unwrap();

    // Recover in THIS process: every acked record, in order; the torn tail truncated.
    let b = Broker::open_with(&log, Durability::Relaxed).unwrap();
    assert_eq!(b.head(), N, "every SIGKILLed-but-acked record recovered");
    assert_eq!(
        std::fs::metadata(&log).unwrap().len(),
        clean_len,
        "the torn tail was truncated off, nothing else"
    );
    let _h = b.serve(&sock2).unwrap();
    let mut sub = Client::connect(&sock2)
        .unwrap()
        .subscribe(0, "/a/rx/>")
        .unwrap();
    for i in 0..N {
        let (off, _s, body) = sub.recv().unwrap().unwrap();
        assert_eq!((off, body), (i, format!("m{}", i + 1).into_bytes()));
    }
    assert_eq!(
        Client::connect(&sock2)
            .unwrap()
            .publish(1, 1, "/a/rx/x", b"dup")
            .unwrap(),
        (0, true),
        "exactly-once ingest survived the kill"
    );
}

/// Recovery (tier-independent) distinguishes a TORN TAIL from CORRUPTION: only an
/// incomplete trailing frame (or an all-zero tail) is truncated on open. A complete
/// frame in the MIDDLE of the log that fails its CRC -- a flipped byte, a foreign file,
/// an older record format -- is refused: open fails `InvalidData` naming the offset and
/// byte, the file is left untouched, and only the explicit `BrokerLog::open_repair`
/// truncates there, reporting the bytes it discarded. Silently truncating would destroy
/// every acked record after the corruption.
#[test]
fn mid_log_corruption_is_refused_not_silently_truncated() {
    use std::io::{Read, Seek, SeekFrom, Write};

    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = format!("/tmp/asrelaxed_corrupt_{pid}_{n}.log");
    let sock = format!("/tmp/asrelaxed_corrupt_{pid}_{n}.sock");
    let _ = std::fs::remove_file(&log);
    let _tmp = Cleanup::new(&[&log, &sock]);
    {
        let b = Broker::open_with(&log, Durability::Relaxed).unwrap();
        let mut h = b.serve(&sock).unwrap();
        let mut p = Client::connect(&sock).unwrap();
        for i in 1..=5u64 {
            p.publish(1, i, "/a/rx/x", format!("m{i}").as_bytes())
                .unwrap();
        }
        drop(p);
        h.shutdown();
    }
    let clean_len = std::fs::metadata(&log).unwrap().len();
    assert_eq!(clean_len % 5, 0, "five identically-sized records");
    let one = clean_len / 5;
    // Flip one byte inside record 2 (the third record): its CRC no longer matches.
    {
        let mut f = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .open(&log)
            .unwrap();
        let at = 2 * one + 20;
        f.seek(SeekFrom::Start(at)).unwrap();
        let mut byte = [0u8; 1];
        f.read_exact(&mut byte).unwrap();
        f.seek(SeekFrom::Start(at)).unwrap();
        f.write_all(&[byte[0] ^ 0xFF]).unwrap();
    }
    let err = Broker::open_with(&log, Durability::Relaxed)
        .err()
        .expect("a corrupt record mid-log must refuse to open");
    assert_eq!(err.kind(), std::io::ErrorKind::InvalidData, "{err}");
    let msg = err.to_string();
    assert!(
        msg.contains("offset 2") && msg.contains("open_repair"),
        "names the offset and the explicit repair path: {msg}"
    );
    assert_eq!(
        std::fs::metadata(&log).unwrap().len(),
        clean_len,
        "refusing to open left the file untouched"
    );
    // The explicit repair truncates at the corrupt record and says what it dropped.
    let (repaired, dropped) =
        astream_broker::BrokerLog::open_repair(&log, Durability::Relaxed).unwrap();
    assert_eq!(repaired.head().0, 2, "the intact prefix");
    assert_eq!(
        dropped,
        3 * one,
        "the corrupt record and everything after it"
    );
    drop(repaired);
    let b2 = Broker::open_with(&log, Durability::Relaxed).unwrap();
    assert_eq!(b2.head(), 2, "reopens normally after the repair");
}
