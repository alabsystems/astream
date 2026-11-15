//! Evidence for `broker.relaxed-tier`: the Relaxed point on the durability dial. An
//! `ack` means the batch is in the OS page cache (NO fsync) — lower latency / higher
//! throughput, the honest trade being it survives a PROCESS crash but not a power loss.
//! What we CAN prove deterministically is that it stays consistent across a PROCESS
//! crash and exactly-once: acked records are delivered, a re-send is deduped, and after
//! a broker restart the log recovers a clean in-order prefix (no corruption, no gaps).
//! We do NOT claim power-loss durability for Relaxed (that is exactly what Strict is
//! for): the device may persist the page cache in any order, so a power loss can leave
//! a hole. What IS claimed is that the loss is announced: the next open, in its new
//! boot, keeps the longest intact prefix above the durable floor and moves the log's
//! generation with lineage, while damage below the floor still refuses
//! (`Durability::Relaxed`).

#![cfg(unix)] // serves the broker on a Unix-domain socket; std has no UDS on Windows

use astream_broker::{Broker, Client, Durability, OpenOptions, Prepared, Volume};
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

/// Relaxed, the boot read from the real kernel, and the log declared ON THE BOOT
/// VOLUME: the kill test asserts the same-boot rule, and its log lives under `/tmp`,
/// which some hosts mount on a device of its own (tmpfs) — where `Volume::Detect`
/// rightly reads it as off the boot volume, and every unclean stop moves the generation.
fn on_the_boot_volume() -> OpenOptions {
    let mut o = OpenOptions::new(Durability::Relaxed);
    o.volume = Volume::Boot;
    o
}

/// The child half of `relaxed_acked_records_survive_a_real_sigkill_of_the_broker`: this
/// test binary re-executes itself running ONLY this function (its suite name,
/// `relaxed_tier::relaxed_child`, with `--exact`) with `ASTREAM_RELAXED_CHILD=<log>|<sock>`
/// set. It serves a RELAXED broker on `<sock>` over `<log>`, prints `listening` once the
/// socket is up, and blocks until it is SIGKILLed — no shutdown, no flush, no fsync ever
/// runs. In a normal `cargo test` run (no env var) it does nothing.
#[test]
fn relaxed_child() {
    let Ok(spec) = std::env::var("ASTREAM_RELAXED_CHILD") else {
        return;
    };
    let (log, sock) = spec.split_once('|').expect("<log>|<sock>");
    let b = Broker::open_opts(log, on_the_boot_volume(), || Ok(Prepared::Nothing))
        .expect("child: open");
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
/// reopen truncates exactly it: across a process crash Relaxed is consistent (no
/// corruption, no gaps); a power loss is another matter (the module docs).
/// Synchronizes on the child's `listening` line and on `wait()` after the kill — no
/// sleeps.
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
        .args(["relaxed_tier::relaxed_child", "--exact", "--nocapture"])
        .env("ASTREAM_RELAXED_CHILD", format!("{log}|{sock}"))
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("spawn the child broker");
    {
        // Sync on data: the child prints `listening` once the socket is bound. A libtest
        // running one test at a time (RUST_TEST_THREADS=1, which the child inherits)
        // writes `test <name> ... ` with no newline before the test runs, so the word
        // ends that line rather than filling one of its own.
        let mut lines = BufReader::new(child.stdout.take().unwrap()).lines();
        loop {
            match lines.next() {
                Some(Ok(l)) if l.trim_end().ends_with("listening") => break,
                Some(Ok(_)) => continue, // the harness's own "running 1 test" line
                other => panic!("child broker did not come up: {other:?}"),
            }
        }
    }

    let mut p = Client::connect(&sock).unwrap();
    let served = p.log_identity().unwrap().expect("the broker names its log");
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
    let b = Broker::open_opts(&log, on_the_boot_volume(), || Ok(Prepared::Nothing)).unwrap();
    assert_eq!(b.head(), N, "every SIGKILLed-but-acked record recovered");
    // The kernel holding the unflushed writes ran throughout (the same boot, read from
    // the real kernel): a process crash moves nothing, and neither does cutting a write
    // that never finished.
    assert_eq!(b.log_identity(), served, "a kill -9 moves nothing");
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

/// The byte offset where each of `bytes`' frames starts, and the end of the last.
fn frame_starts(bytes: &[u8]) -> Vec<usize> {
    let mut starts = vec![0];
    let mut at = 0;
    while at < bytes.len() {
        at += astream_wire::Frame::decode(&bytes[at..])
            .unwrap()
            .expect("a whole frame")
            .consumed;
        starts.push(at);
    }
    starts
}

/// Publish `n` records from producer 1, starting at producer seq `from`.
fn publish_n(log: &mut astream_broker::BrokerLog, from: u64, n: u64) {
    for i in from..from + n {
        log.publish(1, i, "/a/rx/x".into(), format!("m{i}").into_bytes())
            .unwrap();
    }
}

/// What `Durability::Relaxed` says a POWER loss leaves, built as the images it names
/// and checked against what the claim says of each. The device may persist the page
/// cache's blocks in any order and the file's length apart from them, and nothing
/// since the open's fsync is durable. A power loss is a reboot, so the next open runs
/// in another boot (stood in by `Boot::Known`), and the log's sidecar says the run
/// that served it did not stop cleanly in that boot:
///
/// - The log comes back SHORTER (the batches after the open lost from the end): it
///   opens, its generation moved under the same id with lineage at its head — offsets
///   below it name the same records, so a reader resumes there instead of forgetting —
///   and its next append reuses the first lost offset under the NEW identity.
/// - The log comes back with a HOLE above its durable floor (a block that never
///   landed: zeros) and intact records behind it: the open keeps the longest intact
///   prefix, cuts the rest, and moves the generation with lineage at the hole.
/// - Damage BELOW the floor (the bytes the open's own fsync made durable) is no torn
///   write: the open refuses `InvalidData`, the file untouched, and the explicit repair
///   cuts there and moves the generation.
#[test]
fn a_relaxed_power_loss_comes_back_shorter_or_with_a_hole_and_says_which() {
    use astream_broker::{Boot, BrokerLog, OpenOptions, Prepared, Volume};
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let shorter = format!("/tmp/asrelaxed_short_{pid}_{n}.log");
    let holed = format!("/tmp/asrelaxed_hole_{pid}_{n}.log");
    let below = format!("/tmp/asrelaxed_below_{pid}_{n}.log");
    for p in [&shorter, &holed, &below] {
        let _ = std::fs::remove_file(p);
    }
    let _tmp = Cleanup::new(&[&shorter, &holed, &below]);
    // The boot the writing runs serve in, and the one after the power loss.
    const SERVED: [u8; 16] = [0x5E; 16];
    const AFTER: [u8; 16] = [0xAF; 16];
    let open_in = |p: &str, boot: [u8; 16]| {
        let mut o = OpenOptions::new(Durability::Relaxed);
        o.boot = Boot::Known(boot);
        o.volume = Volume::Boot;
        BrokerLog::open_opts(p, o, || Ok(Prepared::Nothing))
    };

    // SHORTER. Three records, then an open (its fsync makes them durable and its
    // sidecar records the floor at head 3), then two more acked into the page cache.
    publish_n(&mut open_in(&shorter, SERVED).unwrap(), 1, 3);
    let (seen, kept) = {
        let mut log = open_in(&shorter, SERVED).unwrap();
        let seen = log.identity();
        let kept = std::fs::metadata(&shorter).unwrap().len();
        publish_n(&mut log, 4, 2);
        assert_eq!(log.head().0, 5);
        (seen, kept)
    };
    // The power loss took the two page-cache batches: the file ends where the open
    // left it.
    std::fs::OpenOptions::new()
        .write(true)
        .open(&shorter)
        .unwrap()
        .set_len(kept)
        .unwrap();
    let mut log = open_in(&shorter, AFTER).expect("a shorter log opens");
    assert_eq!(log.head().0, 3);
    let now = log.identity();
    assert_eq!(
        (now.id, now.generation),
        (seen.id, seen.generation + 1),
        "the generation moved under the same id"
    );
    assert_eq!(
        now.continues(seen, log.lineage()),
        Some(3),
        "offsets below the head still name the records a reader saw"
    );
    assert_eq!(
        log.publish(1, 100, "/a/rx/x".into(), b"after".to_vec())
            .unwrap(),
        (astream_wire::Offset(3), false),
        "the next append reuses the first lost offset, under the new identity"
    );
    drop(log);

    // HOLE. Two records, an open, then three more in the page cache, of which the
    // device kept the second and third but not the first: its bytes read as zeros.
    publish_n(&mut open_in(&holed, SERVED).unwrap(), 1, 2);
    let seen = {
        let mut log = open_in(&holed, SERVED).unwrap();
        publish_n(&mut log, 3, 3);
        log.identity()
    };
    let mut bytes = std::fs::read(&holed).unwrap();
    let starts = frame_starts(&bytes);
    assert_eq!(starts.len(), 6, "five records");
    bytes[starts[2]..starts[3]].fill(0);
    std::fs::write(&holed, &bytes).unwrap();
    let log = open_in(&holed, AFTER).expect("a hole above the floor opens");
    assert_eq!(log.head().0, 2, "the longest intact prefix");
    assert_eq!(log.identity().generation, seen.generation + 1);
    assert_eq!(log.identity().continues(seen, log.lineage()), Some(2));
    drop(log);
    assert_eq!(
        std::fs::read(&holed).unwrap(),
        bytes[..starts[2]],
        "cut at the hole, the intact records behind it included"
    );

    // BELOW THE FLOOR. Three records and an open (the floor at 3); then the second
    // record's block reads as zeros — bytes the open's fsync made durable.
    publish_n(&mut open_in(&below, SERVED).unwrap(), 1, 3);
    let seen = open_in(&below, SERVED).unwrap().identity();
    let mut bytes = std::fs::read(&below).unwrap();
    let starts = frame_starts(&bytes);
    bytes[starts[1]..starts[2]].fill(0);
    std::fs::write(&below, &bytes).unwrap();
    let err = open_in(&below, AFTER)
        .err()
        .expect("damage below the floor must refuse the open");
    assert_eq!(err.kind(), std::io::ErrorKind::InvalidData, "{err}");
    assert!(
        err.to_string().contains("offset 1") && err.to_string().contains("floor"),
        "{err}"
    );
    assert_eq!(
        std::fs::read(&below).unwrap(),
        bytes,
        "the refused open left the file untouched"
    );
    let (log, dropped) = BrokerLog::open_repair(&below, Durability::Relaxed).unwrap();
    assert_eq!(
        (log.head().0, dropped),
        (1, (bytes.len() - starts[1]) as u64),
        "the repair cuts at the damage, the intact records behind it included"
    );
    assert_eq!(
        log.identity(),
        astream_broker::LogIdentity {
            id: seen.id,
            generation: seen.generation + 1,
        },
        "the repair moves the generation under the same id"
    );
}
