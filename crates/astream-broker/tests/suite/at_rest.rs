//! Evidence for `broker.log-encrypted-at-rest`: the durable log — a verbatim
//! recording of every published keystroke and screen frame — is sealed on disk
//! under a key, so a reader of the file recovers nothing without it, recovery with
//! the RIGHT key is lossless and exactly-once, a WRONG key is refused rather than
//! silently discarding data, and a CRC-valid tamper is caught by the AEAD tag.
#![cfg(feature = "at-rest")]

use astream_broker::{BrokerLog, Durability};
use astream_wire::{Frame, Offset};
use std::sync::atomic::{AtomicU64, Ordering};

static CTR: AtomicU64 = AtomicU64::new(0);
const KEY: [u8; 32] = [0x5a; 32];

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

fn tmp(tag: &str) -> (Cleanup, std::path::PathBuf) {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let path = std::env::temp_dir().join(format!("asatrest_{tag}_{pid}_{n}.log"));
    (Cleanup::new(&[&path]), path)
}

fn contains(haystack: &[u8], needle: &[u8]) -> bool {
    haystack.windows(needle.len()).any(|w| w == needle)
}

#[test]
fn encrypts_on_disk_and_recovers_losslessly() {
    let (_tmp, path) = tmp("ok");
    let _ = std::fs::remove_file(&path);

    // Write two sensitive records under encryption, then close the log.
    {
        let mut log = BrokerLog::open_encrypted(&path, KEY).unwrap();
        assert_eq!(
            log.publish(
                1,
                1,
                "/a/stream/term/s1/out".into(),
                b"TOPSECRET-keystrokes".to_vec()
            )
            .unwrap(),
            (Offset(0), false)
        );
        log.publish(
            1,
            2,
            "/a/stream/term/s1/out".into(),
            b"more-secret-output".to_vec(),
        )
        .unwrap();
    }

    // The forensic content is gone from the raw file: neither the bodies nor the
    // subject appear in cleartext.
    let raw = std::fs::read(&path).unwrap();
    assert!(
        !contains(&raw, b"TOPSECRET-keystrokes"),
        "body leaked to disk"
    );
    assert!(
        !contains(&raw, b"more-secret-output"),
        "body leaked to disk"
    );
    assert!(
        !contains(&raw, b"/a/stream/term/s1/out"),
        "subject leaked to disk"
    );

    // Reopen with the same key: full, ordered recovery; exactly-once holds (a
    // re-publish of (1,1) dedups to its original offset).
    {
        let mut log = BrokerLog::open_encrypted(&path, KEY).unwrap();
        let recs = log.read_from(Offset(0));
        assert_eq!(recs.len(), 2);
        assert_eq!(recs[0].subject, "/a/stream/term/s1/out");
        assert_eq!(recs[0].body, b"TOPSECRET-keystrokes");
        assert_eq!(recs[1].body, b"more-secret-output");
        assert_eq!(
            log.publish(1, 1, "x".into(), b"dup".to_vec()).unwrap(),
            (Offset(0), true)
        );
    }
}

#[test]
fn wrong_key_is_refused_not_destroyed() {
    let (_tmp, path) = tmp("wrongkey");
    let _ = std::fs::remove_file(&path);
    {
        let mut log = BrokerLog::open_encrypted(&path, KEY).unwrap();
        log.publish(1, 1, "/a/x".into(), b"data".to_vec()).unwrap();
    }

    let mut wrong = KEY;
    wrong[0] ^= 0xff;
    // A wrong key must be REFUSED — never a silent truncation that would let the
    // broker start fresh and overwrite the (still-encrypted) data.
    assert!(
        BrokerLog::open_encrypted(&path, wrong).is_err(),
        "a wrong key must be refused"
    );
    // The file is untouched: the right key still recovers everything.
    let log = BrokerLog::open_encrypted(&path, KEY).unwrap();
    assert_eq!(log.read_from(Offset(0)).len(), 1);
}

#[test]
fn a_crc_valid_tamper_is_caught_by_the_aead_tag() {
    let (_tmp, path) = tmp("tamper");
    let _ = std::fs::remove_file(&path);
    {
        let mut log = BrokerLog::open_encrypted(&path, KEY).unwrap();
        log.publish(1, 1, "/a/x".into(), b"authentic".to_vec())
            .unwrap();
    }

    // Flip a byte inside the SEALED payload and RE-FRAME it, so the CRC is valid
    // again — the torn-tail check passes and only the AEAD tag can catch this.
    let raw = std::fs::read(&path).unwrap();
    let d = Frame::decode(&raw).unwrap().unwrap();
    let mut payload = d.frame.payload.clone();
    payload[0] ^= 0x01; // corrupt the nonce -> tag verification will fail
    let reframed = Frame::new(payload).encode().unwrap();
    std::fs::write(&path, &reframed).unwrap();

    // The frame decodes (CRC ok) but the record fails to authenticate -> refused.
    assert!(
        BrokerLog::open_encrypted(&path, KEY).is_err(),
        "a CRC-valid tamper must be caught by the AEAD tag"
    );
}

#[test]
fn plaintext_log_still_round_trips_and_is_readable() {
    // The scan-returns-Result refactor must not change the default (unencrypted)
    // path: a plaintext log round-trips, and its body IS visible on disk (the
    // contrast that makes the encryption meaningful).
    let (_tmp, path) = tmp("plain");
    let _ = std::fs::remove_file(&path);
    {
        let mut log = BrokerLog::open(&path).unwrap();
        log.publish(1, 1, "/a/x".into(), b"cleartext-body".to_vec())
            .unwrap();
    }
    let log = BrokerLog::open(&path).unwrap();
    assert_eq!(log.read_from(Offset(0))[0].body, b"cleartext-body");
    let raw = std::fs::read(&path).unwrap();
    assert!(
        contains(&raw, b"cleartext-body"),
        "plaintext log should be readable on disk"
    );
}

#[test]
fn plain_open_on_an_encrypted_log_is_refused_not_wiped() {
    // Using the WRONG constructor (plain open, no key) on an encrypted log must NOT
    // scan-to-empty and set_len(0) it away — it is refused, and the data survives.
    let (_tmp, path) = tmp("noconstructor");
    let _ = std::fs::remove_file(&path);
    {
        let mut log = BrokerLog::open_encrypted(&path, KEY).unwrap();
        log.publish(1, 1, "/a/x".into(), b"precious".to_vec())
            .unwrap();
    }
    let before = std::fs::metadata(&path).unwrap().len();
    // Refused as unreadable bytes — never mistaken for a newer record format, which
    // a sealed payload's random first byte would otherwise look like.
    assert_eq!(
        BrokerLog::open(&path).err().map(|e| e.kind()),
        Some(std::io::ErrorKind::InvalidData),
        "plain open of an encrypted log must be refused"
    );
    let after = std::fs::metadata(&path).unwrap().len();
    assert_eq!(
        before, after,
        "the encrypted log must not be truncated by a refused open"
    );
    // The right constructor still recovers it.
    let log = BrokerLog::open_encrypted(&path, KEY).unwrap();
    assert_eq!(log.read_from(Offset(0)).len(), 1);
}

#[test]
fn a_naive_crc_breaking_flip_is_refused_not_truncated() {
    // The case the adversarial audit caught: a PLAIN single-byte flip breaks the frame
    // CRC, so Frame::decode returns Err (complete-but-corrupt). That must NOT be
    // conflated with a torn tail and silently truncate the record AND its authentic
    // suffix — for an encrypted log it is a hard error.
    let (_tmp, path) = tmp("naiveflip");
    let _ = std::fs::remove_file(&path);
    {
        let mut log = BrokerLog::open_encrypted(&path, KEY).unwrap();
        log.publish(1, 1, "/a/x".into(), b"first".to_vec()).unwrap();
        log.publish(1, 2, "/a/x".into(), b"second-must-survive".to_vec())
            .unwrap();
    }
    // Flip a byte inside record 0's sealed payload (past the 12-byte frame header) —
    // this breaks the CRC without shortening the file.
    let mut raw = std::fs::read(&path).unwrap();
    let before = raw.len() as u64;
    raw[20] ^= 0x01;
    std::fs::write(&path, &raw).unwrap();

    assert!(
        BrokerLog::open_encrypted(&path, KEY).is_err(),
        "a CRC-breaking tamper must be refused, not treated as a torn tail"
    );
    assert_eq!(
        std::fs::metadata(&path).unwrap().len(),
        before,
        "the log must not be truncated by a refused open"
    );
}

/// The byte offset where each of `bytes`' frames starts, and the end of the last.
fn frame_starts(bytes: &[u8]) -> Vec<usize> {
    let mut starts = vec![0];
    let mut at = 0;
    while at < bytes.len() {
        at += Frame::decode(&bytes[at..])
            .unwrap()
            .expect("a whole frame")
            .consumed;
        starts.push(at);
    }
    starts
}

/// A sealed log of `n` records under `KEY` at `durability`, and its bytes.
fn sealed_log(path: &std::path::Path, durability: Durability, n: u64) -> Vec<u8> {
    let mut log = BrokerLog::open_encrypted_with(path, durability, KEY).unwrap();
    for i in 1..=n {
        log.publish(1, i, "/a/x".into(), format!("acked-{i}").into_bytes())
            .unwrap();
    }
    log.bytes()
}

/// Damage the open refuses, on logs SEALED at rest, repaired the way the refusal says.
/// Each lies below the log's durable floor (the reopen that reads the identity records
/// it at the head), where no torn write can be: a Relaxed log whose third record's block
/// reads as zeros with the fourth and fifth intact behind it, and a Strict log, and an
/// Ordered one at aterm's 100 ms horizon (the tier aterm's broker serves), whose fifth
/// record's header lost its last eight bytes (the codec's own encoding of an empty frame:
/// magic, version, flags, eight zero bytes). Each open refuses and names the KEYED repair.
/// The keyless repair refuses too, the file untouched — it reads the first sealed
/// record as an unparseable plaintext one, and its cut would have been the whole log.
/// The keyed repair cuts exactly at the damage and keeps every authentic record before
/// it, readable under the key, and moves the generation under the same id.
#[test]
fn a_sealed_log_is_repaired_with_its_key_and_keeps_its_authentic_prefix() {
    let torn_header = Frame::new(Vec::new()).encode().unwrap();
    assert_eq!(&torn_header[4..], &[0u8; 8], "the torn header's image");
    let ordered = Durability::Ordered {
        horizon: Some(std::time::Duration::from_millis(100)),
    };
    for tier in [Durability::Relaxed, ordered, Durability::Strict] {
        let (_tmp, path) = tmp("keyedrepair");
        let _ = std::fs::remove_file(&path);
        let clean = sealed_log(&path, tier, 5);
        let seen = BrokerLog::open_encrypted_with(&path, tier, KEY)
            .unwrap()
            .identity();
        let starts = frame_starts(&clean);
        assert_eq!(starts.len(), 6, "five records");
        let (damaged, keep) = match tier {
            Durability::Relaxed => {
                let mut b = clean.clone();
                b[starts[2]..starts[3]].fill(0);
                (b, 2)
            }
            Durability::Strict | Durability::Ordered { .. } => {
                let mut b = clean.clone();
                b[starts[4] + 4..starts[4] + 12].fill(0);
                assert_eq!(&b[starts[4]..starts[4] + 12], &torn_header[..]);
                (b, 4)
            }
        };
        std::fs::write(&path, &damaged).unwrap();

        let err = BrokerLog::open_encrypted_with(&path, tier, KEY)
            .err()
            .expect("the damage refuses the open");
        let msg = err.to_string();
        assert_eq!(
            err.kind(),
            std::io::ErrorKind::InvalidData,
            "{tier:?}: {msg}"
        );
        assert!(
            msg.contains(&format!("offset {keep}")) && msg.contains("open_encrypted_repair"),
            "{tier:?}: names the keyed repair: {msg}"
        );
        assert!(
            !msg.contains("BrokerLog::open_repair"),
            "{tier:?}: never the keyless one: {msg}"
        );

        let err = BrokerLog::open_repair(&path, tier)
            .err()
            .expect("the keyless repair refuses a sealed log");
        let msg = err.to_string();
        assert_eq!(
            err.kind(),
            std::io::ErrorKind::InvalidData,
            "{tier:?}: {msg}"
        );
        assert!(msg.contains("open_encrypted_repair"), "{tier:?}: {msg}");
        assert_eq!(
            std::fs::read(&path).unwrap(),
            damaged,
            "{tier:?}: the keyless repair cut nothing"
        );

        let (log, dropped) = BrokerLog::open_encrypted_repair(&path, tier, KEY).unwrap();
        assert_eq!(
            (log.head(), dropped),
            (Offset(keep), (damaged.len() - starts[keep as usize]) as u64),
            "{tier:?}: the cut is at the damage"
        );
        assert_eq!(log.identity().id, seen.id, "{tier:?}");
        assert_eq!(log.identity().generation, seen.generation + 1, "{tier:?}");
        drop(log);
        let log = BrokerLog::open_encrypted_with(&path, tier, KEY).unwrap();
        let bodies: Vec<Vec<u8>> = log
            .read_from(Offset(0))
            .iter()
            .map(|r| r.body.clone())
            .collect();
        let want: Vec<Vec<u8>> = (1..=keep)
            .map(|i| format!("acked-{i}").into_bytes())
            .collect();
        assert_eq!(bodies, want, "{tier:?}: every authentic record before it");
    }
}

/// The power-loss image a Strict log is promised to survive, on a log sealed at rest:
/// a header torn after its first four bytes past the newest batch, above the durable
/// floor. Once a sealing build has opened the log, the open never refuses that: the torn
/// write is cut, every authentic record kept, and nothing moves (it never finished, so
/// it was never acked).
#[test]
fn a_header_torn_past_the_floor_opens_with_the_header_cut() {
    let torn_header = Frame::new(Vec::new()).encode().unwrap();
    let (_tmp, path) = tmp("tornpastfloor");
    let _ = std::fs::remove_file(&path);
    let clean = sealed_log(&path, Durability::Strict, 3);
    let seen = BrokerLog::open_encrypted_with(&path, Durability::Strict, KEY)
        .unwrap()
        .identity();
    let mut damaged = clean.clone();
    damaged.extend_from_slice(&torn_header);
    std::fs::write(&path, &damaged).unwrap();
    let log = BrokerLog::open_encrypted_with(&path, Durability::Strict, KEY)
        .expect("a torn header above the floor opens");
    assert_eq!(log.head(), Offset(3));
    assert_eq!(log.identity(), seen, "nothing moved");
    drop(log);
    assert_eq!(
        std::fs::read(&path).unwrap(),
        clean,
        "the torn header was cut"
    );
}

/// The keyed repair never cuts a record that fails to AUTHENTICATE: that frame is
/// intact (its CRC holds), so no crash made it. A WRONG key fails the very first
/// record, and a cut there would discard the whole log; a record rewritten without
/// the key (re-framed, so its CRC holds) fails mid-log; a plaintext log read under a
/// key fails at its first record. Each is refused `InvalidData` with the file
/// untouched, and the right constructor still reads everything.
#[test]
fn the_keyed_repair_never_cuts_a_record_that_fails_to_authenticate() {
    let mut wrong = KEY;
    wrong[0] ^= 0xff;

    let (_tmp, path) = tmp("repairwrongkey");
    let _ = std::fs::remove_file(&path);
    let clean = sealed_log(&path, Durability::Strict, 3);
    let err = BrokerLog::open_encrypted_repair(&path, Durability::Strict, wrong)
        .err()
        .expect("a wrong key must not repair");
    assert_eq!(err.kind(), std::io::ErrorKind::InvalidData, "{err}");
    assert!(err.to_string().contains("authenticate"), "{err}");
    assert_eq!(std::fs::read(&path).unwrap(), clean, "wrong key: untouched");

    let starts = frame_starts(&clean);
    let mut tampered = clean[..starts[1]].to_vec();
    let mut payload = Frame::decode(&clean[starts[1]..])
        .unwrap()
        .unwrap()
        .frame
        .payload;
    payload[0] ^= 0x01;
    tampered.extend_from_slice(&Frame::new(payload).encode().unwrap());
    tampered.extend_from_slice(&clean[starts[2]..]);
    std::fs::write(&path, &tampered).unwrap();
    let err = BrokerLog::open_encrypted_repair(&path, Durability::Strict, KEY)
        .err()
        .expect("a rewritten record must not be cut");
    assert_eq!(err.kind(), std::io::ErrorKind::InvalidData, "{err}");
    assert!(err.to_string().contains("offset 1"), "{err}");
    assert_eq!(std::fs::read(&path).unwrap(), tampered, "tamper: untouched");

    let (_tmp2, plain) = tmp("repairplainunderkey");
    let _ = std::fs::remove_file(&plain);
    let plain_bytes = {
        let mut log = BrokerLog::open(&plain).unwrap();
        log.publish(1, 1, "/a/x".into(), b"plaintext".to_vec())
            .unwrap();
        log.bytes()
    };
    let err = BrokerLog::open_encrypted_repair(&plain, Durability::Strict, KEY)
        .err()
        .expect("a plaintext log must not be cut under a key");
    assert_eq!(err.kind(), std::io::ErrorKind::InvalidData, "{err}");
    assert_eq!(
        std::fs::read(&plain).unwrap(),
        plain_bytes,
        "plain: untouched"
    );
    assert_eq!(BrokerLog::open(&plain).unwrap().head(), Offset(1));
}

fn sidecar_path(log: &std::path::Path, suffix: &str) -> std::path::PathBuf {
    let mut s = log.as_os_str().to_os_string();
    s.push(suffix);
    std::path::PathBuf::from(s)
}

#[test]
fn cross_log_record_and_seal_splice_under_same_key_is_refused() {
    let (_tmp_a, path_a) = tmp("splice_a");
    let (_tmp_b, path_b) = tmp("splice_b");
    let _ = std::fs::remove_file(&path_a);
    let _ = std::fs::remove_file(&path_b);

    let (seal_a, seal_b) = {
        let mut log_a = BrokerLog::open_encrypted_bound(&path_a, KEY).unwrap();
        let mut log_b = BrokerLog::open_encrypted_bound(&path_b, KEY).unwrap();
        let sa = log_a.at_rest_seal_id().expect("v2 bound log has seal_id");
        let sb = log_b.at_rest_seal_id().expect("v2 bound log has seal_id");
        assert_ne!(sa, sb, "distinct logs mint distinct 256-bit seal_ids");

        log_a
            .publish(1, 1, "/a/a0".into(), b"alpha-0".to_vec())
            .unwrap();
        log_a
            .publish(1, 2, "/a/a1".into(), b"alpha-1".to_vec())
            .unwrap();
        log_b
            .publish(2, 1, "/a/b0".into(), b"bravo-0".to_vec())
            .unwrap();
        log_b
            .publish(2, 2, "/a/b1".into(), b"bravo-1".to_vec())
            .unwrap();
        (sa, sb)
    };

    assert!(sidecar_path(&path_a, ".seal").exists());
    assert!(sidecar_path(&path_b, ".seal").exists());
    assert_ne!(seal_a, seal_b);

    let bytes_a = std::fs::read(&path_a).unwrap();
    let bytes_b = std::fs::read(&path_b).unwrap();
    let starts_a = frame_starts(&bytes_a);
    let starts_b = frame_starts(&bytes_b);

    // 1. Cross-log record splice at the SAME offset (index 1) under the SAME 256-bit key:
    // record 0 from A followed by record 1 from B.
    let mut spliced = bytes_a[..starts_a[1]].to_vec();
    spliced.extend_from_slice(&bytes_b[starts_b[1]..starts_b[2]]);
    std::fs::write(&path_a, &spliced).unwrap();
    let err = BrokerLog::open_encrypted(&path_a, KEY)
        .err()
        .expect("cross-log record splice under the same key must fail AEAD authentication");
    assert_eq!(err.kind(), std::io::ErrorKind::InvalidData, "{err}");
    assert!(err.to_string().contains("authenticate"), "{err}");

    // Restore clean log_a and verify normal reopen still succeeds with matching seal_id.
    std::fs::write(&path_a, &bytes_a).unwrap();
    {
        let log_a = BrokerLog::open_encrypted_bound(&path_a, KEY).unwrap();
        assert_eq!(log_a.at_rest_seal_id(), Some(seal_a));
        assert_eq!(log_a.head(), Offset(2));
    }

    // 2. Cross-log `<log>.seal` swap under the same key -> refused.
    let raw_seal_a = std::fs::read(sidecar_path(&path_a, ".seal")).unwrap();
    let raw_seal_b = std::fs::read(sidecar_path(&path_b, ".seal")).unwrap();
    std::fs::write(sidecar_path(&path_a, ".seal"), &raw_seal_b).unwrap();
    assert!(
        BrokerLog::open_encrypted(&path_a, KEY).is_err(),
        "swapping another log's .seal must fail authentication"
    );

    // 3. Deleting `<log>.seal` on a non-empty log -> refused by both open_encrypted_bound
    // and open_encrypted (because records carry v2 bound AAD, not legacy v1 offset AAD!).
    std::fs::remove_file(sidecar_path(&path_a, ".seal")).unwrap();
    assert!(
        BrokerLog::open_encrypted_bound(&path_a, KEY).is_err(),
        "open_encrypted_bound must refuse a non-empty log missing .seal"
    );
    assert!(
        BrokerLog::open_encrypted(&path_a, KEY).is_err(),
        "v2 bound ciphertext cannot downgrade to v1 unbound AAD when .seal is deleted"
    );

    // Restoring the authentic `<log>.seal` recovers every record losslessly.
    std::fs::write(sidecar_path(&path_a, ".seal"), &raw_seal_a).unwrap();
    let log_a = BrokerLog::open_encrypted_bound(&path_a, KEY).unwrap();
    let bodies: Vec<Vec<u8>> = log_a
        .read_from(Offset(0))
        .iter()
        .map(|r| r.body.clone())
        .collect();
    assert_eq!(bodies, vec![b"alpha-0".to_vec(), b"alpha-1".to_vec()]);
}

#[cfg(all(feature = "retention", feature = "anti-rollback"))]
#[test]
fn cross_log_state_held_and_watermark_sidecar_splice_under_same_key_is_refused() {
    use astream_broker::retention::{Retention, Rule};
    use astream_broker::{Broker, Client};

    let (_tmp_a, path_a) = tmp("sidecar_a");
    let (_tmp_b, path_b) = tmp("sidecar_b");
    let _ = std::fs::remove_file(&path_a);
    let _ = std::fs::remove_file(&path_b);

    let rules = Retention::new(
        vec![
            Rule::prefix("/a/stream/>").unwrap().max_bytes(60),
            Rule::hold("/a/in/>").unwrap().max_bytes(64 * 1024),
        ],
        Rule::default_hold(),
    )
    .unwrap();

    for (p, label) in [(&path_a, "alpha"), (&path_b, "bravo")] {
        let broker = Broker::open_encrypted_verified_init(p, KEY).unwrap();
        broker.set_retention(rules.clone()).unwrap();
        let mut srv = broker.serve_tcp("127.0.0.1:0").unwrap();
        let addr = srv.tcp_addr().unwrap().to_owned();
        let mut cli = Client::connect_tcp(&addr).unwrap();
        cli.publish(1, 1, "/a/in/mail", format!("mail-{label}").as_bytes())
            .unwrap();
        cli.publish(1, 2, "/a/lv/node", format!("presence-{label}").as_bytes())
            .unwrap();
        for i in 3..=8u64 {
            cli.publish(
                1,
                i,
                "/a/stream/out",
                format!("{label}-payload-{i}").as_bytes(),
            )
            .unwrap();
        }
        let _ = broker.retention_tick_at(2_000).unwrap();
        drop(cli);
        srv.shutdown();
    }

    let state_a = std::fs::read(sidecar_path(&path_a, ".state")).unwrap();
    let state_b = std::fs::read(sidecar_path(&path_b, ".state")).unwrap();
    let held_a = std::fs::read(sidecar_path(&path_a, ".held")).unwrap();
    let held_b = std::fs::read(sidecar_path(&path_b, ".held")).unwrap();
    let hw_a = std::fs::read(sidecar_path(&path_a, ".hw")).unwrap();
    let hw_b = std::fs::read(sidecar_path(&path_b, ".hw")).unwrap();

    // 1. Splice `<log_b>.state` onto `<log_a>.state` (same base, same KEY!).
    std::fs::write(sidecar_path(&path_a, ".state"), &state_b).unwrap();
    assert!(
        BrokerLog::open_encrypted_verified(&path_a, KEY).is_err(),
        "cross-log .state splice under same key must be refused"
    );
    std::fs::write(sidecar_path(&path_a, ".state"), &state_a).unwrap();

    // 2. Splice `<log_b>.held` onto `<log_a>.held` (same KEY!).
    std::fs::write(sidecar_path(&path_a, ".held"), &held_b).unwrap();
    assert!(
        BrokerLog::open_encrypted_verified(&path_a, KEY).is_err(),
        "cross-log .held splice under same key must be refused"
    );
    std::fs::write(sidecar_path(&path_a, ".held"), &held_a).unwrap();

    // 3. Splice `<log_b>.hw` onto `<log_a>.hw` (same base, same head, same KEY!).
    std::fs::write(sidecar_path(&path_a, ".hw"), &hw_b).unwrap();
    assert!(
        BrokerLog::open_encrypted_verified(&path_a, KEY).is_err(),
        "cross-log .hw splice under same key must be refused"
    );
    std::fs::write(sidecar_path(&path_a, ".hw"), &hw_a).unwrap();

    // Authentic sidecars reopen cleanly and preserve held mail + stream tail.
    let log_a = BrokerLog::open_encrypted_verified(&path_a, KEY).unwrap();
    assert!(log_a.base().0 >= 3);
    assert_eq!(log_a.head(), Offset(8));
}

#[cfg(all(unix, feature = "cap", feature = "anti-rollback"))]
#[test]
fn broker_open_guarded_encrypted_and_sharded_open_opts_enforce_t12() {
    use astream_broker::{AntiRollback, Broker, Client, OpenOptions, ShardedBroker};
    use astream_cap::mint;

    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("ast12_{}_{}", std::process::id(), n));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    struct DirCleanup(std::path::PathBuf);
    impl Drop for DirCleanup {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    let _guard = DirCleanup(dir.clone());

    let secret = b"t12-capability-mint-secret-0123456789abcdef";
    let log_path = dir.join("guarded.log");
    let sock_path = dir.join("guarded.sock");

    let cap_rw = mint(secret, "rw:/a/t12/>").unwrap();
    let cap_ro = mint(secret, "ro:/a/t12/>").unwrap();

    // 1. Single-broker T12: capabilities + bound at-rest encryption + anti-rollback.
    {
        let broker =
            Broker::open_guarded_encrypted_verified_init(&log_path, secret.to_vec(), KEY).unwrap();
        let mut srv = broker.serve(&sock_path).unwrap();

        // Unattached client cannot publish on a guarded broker.
        let mut unauth = Client::connect(&sock_path).unwrap();
        assert!(unauth.publish(1, 1, "/a/t12/one", b"forbid").is_err());

        let mut cli = Client::connect(&sock_path).unwrap();
        cli.attach(&cap_rw.filter, &cap_rw.tag).unwrap();
        let (off0, dup0) = cli
            .publish(1, 1, "/a/t12/one", b"t12-confidential-payload-0")
            .unwrap();
        let (off1, dup1) = cli
            .publish(1, 2, "/a/t12/two", b"t12-confidential-payload-1")
            .unwrap();
        assert_eq!((off0, dup0, off1, dup1), (0, false, 1, false));
        srv.shutdown();
    }

    let raw = std::fs::read(&log_path).unwrap();
    assert!(!contains(&raw, b"t12-confidential-payload"));
    assert!(!contains(&raw, b"/a/t12/one"));
    assert!(sidecar_path(&log_path, ".seal").exists());
    assert!(sidecar_path(&log_path, ".hw").exists());
    let len_at_1 = std::fs::OpenOptions::new()
        .read(true)
        .open(&log_path)
        .unwrap()
        .metadata()
        .unwrap()
        .len();
    assert!(len_at_1 > 0);

    // Reopen with verified guard + encryption and fetch records over socket.
    {
        let broker =
            Broker::open_guarded_encrypted_verified(&log_path, secret.to_vec(), KEY).unwrap();
        let mut srv = broker.serve(&sock_path).unwrap();
        let mut cli = Client::connect(&sock_path).unwrap();
        cli.attach(&cap_ro.filter, &cap_ro.tag).unwrap();
        let (recs, (_next, _head)) = cli.fetch(0, "/a/t12/>", 16).unwrap();
        assert_eq!(recs.len(), 2);
        assert_eq!(recs[0].2, b"t12-confidential-payload-0");
        assert_eq!(recs[1].2, b"t12-confidential-payload-1");
        srv.shutdown();
    }

    // Truncating the guarded encrypted log is caught by anti-rollback on reopen.
    let starts = frame_starts(&raw);
    std::fs::OpenOptions::new()
        .write(true)
        .open(&log_path)
        .unwrap()
        .set_len(starts[1] as u64)
        .unwrap();
    assert!(
        Broker::open_guarded_encrypted_verified(&log_path, secret.to_vec(), KEY).is_err(),
        "rolled-back guarded encrypted log must be refused"
    );

    // 2. ShardedBroker::open_opts: independent `<shard-i.log>.seal` bindings across 4 shards.
    let shard_logs = dir.join("shards-log");
    let shard_socks = dir.join("shards-sock");
    let cap_shard = mint(secret, "rw:/a/shard/>").unwrap();
    {
        let mut opts = OpenOptions::new(Durability::Strict);
        opts.guard = Some(secret.to_vec());
        opts.at_rest_key = Some(KEY);
        opts.require_bound_at_rest = true;
        opts.anti_rollback = AntiRollback::Init;

        let sb = ShardedBroker::open_opts(&shard_logs, 4, opts).unwrap();
        let mut sh = sb.serve(&shard_socks).unwrap();
        for i in 0..4u32 {
            let mut cli = Client::connect(shard_socks.join(format!("shard-{i}.sock"))).unwrap();
            cli.attach(&cap_shard.filter, &cap_shard.tag).unwrap();
            cli.publish(
                100 + u64::from(i),
                1,
                &format!("/a/shard/k{i}"),
                format!("shard-secret-{i}").as_bytes(),
            )
            .unwrap();
        }
        sh.shutdown();
    }

    // Every shard has its own `.seal` and `.hw`, and splicing shard-1.log.seal onto shard-0
    // is refused on reopen once shard-0 holds ciphertext.
    for i in 0..4u32 {
        let sp = shard_logs.join(format!("shard-{i}.log"));
        assert!(
            sidecar_path(&sp, ".seal").exists(),
            "shard {i} missing .seal"
        );
        assert!(sidecar_path(&sp, ".hw").exists(), "shard {i} missing .hw");
        let sraw = std::fs::read(&sp).unwrap();
        assert!(!contains(&sraw, b"shard-secret-"));
    }
    let seal0 = std::fs::read(sidecar_path(&shard_logs.join("shard-0.log"), ".seal")).unwrap();
    let seal1 = std::fs::read(sidecar_path(&shard_logs.join("shard-1.log"), ".seal")).unwrap();
    std::fs::write(
        sidecar_path(&shard_logs.join("shard-0.log"), ".seal"),
        &seal1,
    )
    .unwrap();
    {
        let mut opts = OpenOptions::new(Durability::Strict);
        opts.guard = Some(secret.to_vec());
        opts.at_rest_key = Some(KEY);
        opts.require_bound_at_rest = true;
        opts.anti_rollback = AntiRollback::Verify;
        assert!(
            ShardedBroker::open_opts(&shard_logs, 4, opts).is_err(),
            "cross-shard .seal swap must fail on ShardedBroker reopen"
        );
    }
    std::fs::write(
        sidecar_path(&shard_logs.join("shard-0.log"), ".seal"),
        &seal0,
    )
    .unwrap();
    {
        let mut opts = OpenOptions::new(Durability::Strict);
        opts.guard = Some(secret.to_vec());
        opts.at_rest_key = Some(KEY);
        opts.require_bound_at_rest = true;
        opts.anti_rollback = AntiRollback::Verify;
        let sb = ShardedBroker::open_opts(&shard_logs, 4, opts).unwrap();
        assert_eq!(sb.shards(), 4);
    }
}

#[cfg(all(
    unix,
    feature = "cap",
    feature = "anti-rollback",
    feature = "retention"
))]
#[test]
fn asb_cli_at_rest_serve_compact_stats_repair_and_argv_refusal() {
    use std::io::{BufRead, BufReader, Write as _};
    use std::os::unix::fs::PermissionsExt as _;
    use std::process::{Command, Stdio};

    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("asb_atrest_{}_{}", std::process::id(), n));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    struct DirCleanup(std::path::PathBuf);
    impl Drop for DirCleanup {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    let _guard = DirCleanup(dir.clone());

    let log_p = dir.join("cli.log");
    let sock_p = dir.join("cli.sock");
    let sec_p = dir.join("secret.key");
    let ark_p = dir.join("atrest.key");
    let cap_p = dir.join("all.cap");

    std::fs::write(&sec_p, b"cli-at-rest-mint-secret-0123456789abcdef\n").unwrap();
    std::fs::set_permissions(&sec_p, std::fs::Permissions::from_mode(0o600)).unwrap();
    std::fs::write(
        &ark_p,
        b"5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a\n",
    )
    .unwrap();
    std::fs::set_permissions(&ark_p, std::fs::Permissions::from_mode(0o600)).unwrap();

    let asb = || Command::new(env!("CARGO_BIN_EXE_asb"));

    // 1. `--at-rest-key` on argv is refused (exit 2) before opening any file.
    let bad = asb()
        .args([
            "serve",
            sock_p.to_str().unwrap(),
            log_p.to_str().unwrap(),
            "--at-rest-key",
            "5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a",
        ])
        .output()
        .unwrap();
    assert_eq!(bad.status.code(), Some(2));
    assert!(!log_p.exists());

    // 2. `--anti-rollback` without an at-rest key or with non-strict durability is refused (exit 2).
    let no_key = asb()
        .args([
            "serve",
            sock_p.to_str().unwrap(),
            log_p.to_str().unwrap(),
            "--anti-rollback-init",
        ])
        .output()
        .unwrap();
    assert_eq!(no_key.status.code(), Some(2));

    let relaxed_ar = asb()
        .args([
            "serve",
            sock_p.to_str().unwrap(),
            log_p.to_str().unwrap(),
            "--durability",
            "relaxed",
            "--at-rest-key-file",
            ark_p.to_str().unwrap(),
            "--anti-rollback-init",
        ])
        .output()
        .unwrap();
    assert_eq!(relaxed_ar.status.code(), Some(2));

    // Mint rw+ro capability file for `/a/cli/>`.
    let pub_mint = asb()
        .args([
            "mint",
            "rw,p=n-cli:/a/cli/>",
            "--secret-file",
            sec_p.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        pub_mint.status.success(),
        "mint rw failed: {}",
        String::from_utf8_lossy(&pub_mint.stderr)
    );
    let sub_mint = asb()
        .args([
            "mint",
            "ro:/a/cli/>",
            "--secret-file",
            sec_p.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        sub_mint.status.success(),
        "mint ro failed: {}",
        String::from_utf8_lossy(&sub_mint.stderr)
    );
    let mut caps_txt = Vec::new();
    caps_txt.extend_from_slice(&pub_mint.stdout);
    caps_txt.extend_from_slice(&sub_mint.stdout);
    std::fs::write(&cap_p, &caps_txt).unwrap();
    std::fs::set_permissions(&cap_p, std::fs::Permissions::from_mode(0o600)).unwrap();

    // 3. Start `asb serve` with guard + bound at-rest encryption + anti-rollback-init.
    let mut srv = asb()
        .args([
            "serve",
            sock_p.to_str().unwrap(),
            log_p.to_str().unwrap(),
            "--secret-file",
            sec_p.to_str().unwrap(),
            "--at-rest-key-file",
            ark_p.to_str().unwrap(),
            "--anti-rollback-init",
        ])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let mut ready = String::new();
    BufReader::new(srv.stdout.take().unwrap())
        .read_line(&mut ready)
        .unwrap();
    assert!(
        ready.starts_with("listening "),
        "unexpected line: {ready:?}"
    );

    for i in 0..4u32 {
        let mut p = asb()
            .args([
                "pub",
                sock_p.to_str().unwrap(),
                &format!("/a/cli/m{i}"),
                "--cap-file",
                cap_p.to_str().unwrap(),
            ])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        p.stdin
            .take()
            .unwrap()
            .write_all(format!("cli-secret-body-{i}").as_bytes())
            .unwrap();
        let out = p.wait_with_output().unwrap();
        assert!(
            out.status.success(),
            "pub {i} failed: {}",
            String::from_utf8_lossy(&out.stderr)
        );
    }

    let _ = srv.kill();
    let _ = srv.wait();
    let _ = std::fs::remove_file(&sock_p);

    let raw_log = std::fs::read(&log_p).unwrap();
    assert!(!contains(&raw_log, b"cli-secret-body-"));
    assert!(sidecar_path(&log_p, ".seal").exists());
    assert!(sidecar_path(&log_p, ".hw").exists());

    // 4. `asb compact` and `asb stats` under `--at-rest-key-file`.
    let comp = asb()
        .args([
            "compact",
            log_p.to_str().unwrap(),
            "2",
            "--at-rest-key-file",
            ark_p.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        comp.status.success(),
        "compact failed: {}",
        String::from_utf8_lossy(&comp.stderr)
    );

    let st = asb()
        .args([
            "stats",
            log_p.to_str().unwrap(),
            "--at-rest-key-file",
            ark_p.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        st.status.success(),
        "stats failed: {}",
        String::from_utf8_lossy(&st.stderr)
    );
    let st_out = String::from_utf8_lossy(&st.stdout);
    assert!(
        st_out.contains("base=2") && (st_out.contains("head=4") || st_out.contains("head=5")),
        "unexpected stats output: {st_out:?}"
    );

    // 5. Reopen `asb serve` with `--anti-rollback` (verifying re-identified `.hw` after compact!).
    let mut srv2 = asb()
        .args([
            "serve",
            sock_p.to_str().unwrap(),
            log_p.to_str().unwrap(),
            "--secret-file",
            sec_p.to_str().unwrap(),
            "--at-rest-key-file",
            ark_p.to_str().unwrap(),
            "--anti-rollback",
        ])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let mut ready2 = String::new();
    BufReader::new(srv2.stdout.take().unwrap())
        .read_line(&mut ready2)
        .unwrap();
    assert!(
        ready2.starts_with("listening "),
        "unexpected line: {ready2:?}"
    );

    let fetched = asb()
        .args([
            "fetch",
            sock_p.to_str().unwrap(),
            "/a/cli/>",
            "--from",
            "2",
            "--cap-file",
            cap_p.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        fetched.status.success(),
        "fetch failed: {}",
        String::from_utf8_lossy(&fetched.stderr)
    );
    let fetched_out = String::from_utf8_lossy(&fetched.stdout);
    assert!(fetched_out.contains("cli-secret-body-2"));
    assert!(fetched_out.contains("cli-secret-body-3"));

    let _ = srv2.kill();
    let _ = srv2.wait();

    // 6. Keyed `asb repair` cuts a damaged tail while keyless `asb repair` refuses.
    let mut damaged = std::fs::read(&log_p).unwrap();
    let torn_hdr = Frame::new(Vec::new()).encode().unwrap();
    // Corrupt last record header into an empty frame so plain open refuses below durable floor.
    let starts = frame_starts(&damaged);
    let last_start = starts[starts.len() - 2];
    damaged[last_start..last_start + 12].copy_from_slice(&torn_hdr);
    std::fs::write(&log_p, &damaged).unwrap();

    let keyless_rep = asb()
        .args(["repair", log_p.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(
        !keyless_rep.status.success(),
        "keyless repair must refuse sealed log"
    );

    let keyed_rep = asb()
        .args([
            "repair",
            log_p.to_str().unwrap(),
            "--at-rest-key-file",
            ark_p.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        keyed_rep.status.success(),
        "keyed repair failed: {}",
        String::from_utf8_lossy(&keyed_rep.stderr)
    );
}

/// AT-REST NAMES ITS CIPHER, NEVER THE SEALED WIRE: in the crate's manifest the `at-rest`
/// feature pulls `dep:astream-aead` itself and names none of the features that compile the
/// sealed TCP transport (`aead`, `handshake`, `identity`), and `anti-rollback` still implies
/// `at-rest`. An embedder that keeps its bus on one machine (aterm, whose third-party audit
/// rests on no feature of its reaching `aead`) seals its log without compiling the wire.
/// NC: `at-rest = ["aead"]`, the manifest before it, fails here (and the feature tree then
/// shows `astream-broker feature "aead"` under `at-rest`).
#[test]
fn at_rest_names_its_cipher_never_the_sealed_wire() {
    let manifest = include_str!("../../Cargo.toml");
    let features = |name: &str| -> Vec<String> {
        let line = manifest
            .lines()
            .find(|l| l.trim_start().starts_with(&format!("{name} = [")))
            .unwrap_or_else(|| panic!("Cargo.toml declares no `{name}` feature"));
        let inner = line.split_once('[').and_then(|(_, r)| r.split_once(']'));
        let (list, _) = inner.unwrap_or_else(|| panic!("`{name}` is not one line: {line}"));
        list.split(',')
            .map(|f| f.trim().trim_matches('"').to_string())
            .filter(|f| !f.is_empty())
            .collect()
    };
    let at_rest = features("at-rest");
    assert_eq!(
        at_rest,
        vec!["dep:astream-aead".to_string()],
        "at-rest = {at_rest:?}"
    );
    assert!(
        features("anti-rollback").contains(&"at-rest".to_string()),
        "anti-rollback implies at-rest"
    );
}

/// AT-REST ALONE COMPILES NO SEALED WIRE: built with `at-rest` and not `aead` (the claim's
/// `--no-default-features --features at-rest`), neither `Broker::serve_tcp_sealed` nor
/// `Client::connect_tcp_sealed` exists, nor astream-aead's `SealedStream`. Each path below resolves to the stand-in trait's
/// item only because the type has no item of its own by that name (an inherent item wins
/// over a trait's): were either compiled, its own signature would not fit and this module
/// would not compile.
#[cfg(not(feature = "aead"))]
mod no_sealed_wire {
    use astream_broker::{Broker, Client};

    trait NoServeSealed {
        fn serve_tcp_sealed(&self) -> bool {
            false
        }
    }
    impl NoServeSealed for Broker {}

    trait NoConnectSealed {
        fn connect_tcp_sealed() -> bool {
            false
        }
    }
    impl NoConnectSealed for Client {}

    #[test]
    fn at_rest_alone_compiles_no_sealed_wire() {
        let serve: fn(&Broker) -> bool = Broker::serve_tcp_sealed;
        let _ = serve;
        assert!(!Client::connect_tcp_sealed());
    }

    /// Nor astream-aead's `SealedStream`, the record layer and hello handshake the sealed wire
    /// speaks: under at-rest the broker asks astream-aead for seal/open alone, never its
    /// `stream` feature. `SealedStream` below names the stand-in only because astream-aead's
    /// glob exports none: were it compiled, the two globs would make the name ambiguous and
    /// this module would not compile (NC: `at-rest = ["dep:astream-aead",
    /// "astream-aead/stream"]` fails it so, E0659).
    mod no_sealed_stream {
        mod stand_in {
            pub struct SealedStream;
        }
        use astream_aead::*;
        use stand_in::*;

        #[test]
        fn at_rest_alone_compiles_no_sealed_stream() {
            let _: SealedStream = SealedStream;
            assert_eq!(
                OVERHEAD,
                NONCE_LEN + TAG_LEN,
                "astream-aead's seal/open is here"
            );
        }
    }
}
