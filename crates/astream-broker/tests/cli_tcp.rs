//! Claim `broker.cli.tcp-roundtrip`: `asb --tcp` puts bytes on the bus and tails
//! them back byte-exactly over PLAINTEXT TCP — the cross-machine transport for a
//! trusted network (the sealed transport is `--key-env`/`--key-file`, tested
//! below under the `aead` feature and in `sealed_transport`). serve binds
//! `host:0` and prints the OS-chosen address, so the test learns the port with no
//! fixed-port flakiness and no sleeps. The framing is pinned exactly: the header's
//! offset is the one `pub` printed and the body is followed by one newline.
#![cfg(unix)]

use std::io::{BufRead, BufReader, Write};
use std::process::{Child, Command, Output, Stdio};
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

/// Remove `path` (a file or a directory) and every `<path>.*` sidecar beside it.
fn remove_with_sidecars(path: impl AsRef<std::path::Path>) {
    let path = path.as_ref();
    let _ = std::fs::remove_file(path);
    let _ = std::fs::remove_dir_all(path);
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

fn fresh_log(tag: &str) -> (Cleanup, String) {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let log = format!("/tmp/asbtcp_{tag}_{}_{n}.log", std::process::id());
    let _ = std::fs::remove_file(&log);
    (Cleanup::new(&[&log]), log)
}

fn asb() -> Command {
    Command::new(env!("CARGO_BIN_EXE_asb"))
}

/// A serving broker (killed + reaped on drop) and the address it printed.
struct Serve(Child);

impl Drop for Serve {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

/// `asb serve 127.0.0.1:0 <log> <extra...>`; returns the bound address (data-sync).
fn serve(log: &str, extra: &[&str]) -> (Serve, String) {
    let mut serve = asb()
        .args(["serve", "127.0.0.1:0", log])
        .args(extra)
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let mut r = BufReader::new(serve.stdout.take().unwrap());
    let mut line = String::new();
    r.read_line(&mut line).unwrap();
    assert!(
        line.starts_with("listening 127.0.0.1:"),
        "readiness: {line:?}"
    );
    let addr = line.trim().trim_start_matches("listening ").to_string();
    (Serve(serve), addr)
}

fn publish(addr: &str, subject: &str, extra: &[&str], body: &[u8]) -> Output {
    let mut c = asb()
        .args(["pub", addr, subject])
        .args(extra)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    c.stdin.take().unwrap().write_all(body).unwrap();
    c.wait_with_output().unwrap()
}

fn stdout(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).into_owned()
}
fn stderr(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

/// One framed delivery, asserting the exact `<offset> <nbytes>\n<body>\n` shape.
fn read_record(r: &mut impl BufRead) -> (u64, Vec<u8>) {
    let mut header = String::new();
    r.read_line(&mut header).unwrap();
    assert!(header.ends_with('\n'), "header line: {header:?}");
    let parts: Vec<&str> = header.trim_end_matches('\n').split(' ').collect();
    assert_eq!(parts.len(), 2, "framing header: {header:?}");
    let offset: u64 = parts[0].parse().expect("offset field");
    let nbytes: usize = parts[1].parse().expect("nbytes field");
    let mut body = vec![0u8; nbytes];
    r.read_exact(&mut body).unwrap();
    let mut nl = [0u8; 1];
    r.read_exact(&mut nl).unwrap();
    assert_eq!(nl, [b'\n'], "exactly one newline terminates the body");
    (offset, body)
}

#[test]
fn asb_tcp_pub_sub_roundtrip() {
    let (_tmp, log) = fresh_log("plain");
    let (_s, addr) = serve(&log, &["--tcp"]);

    let mut sub = asb()
        .args(["sub", &addr, "/a/stream/x", "--tcp"])
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();

    let first: &[u8] = b"tcp\x00cross\nmachine";
    let second: &[u8] = b"\nsecond\x00";
    let out = publish(
        &addr,
        "/a/stream/x",
        &["--id", "1", "--seq", "1", "--tcp"],
        first,
    );
    assert_eq!(stdout(&out), "0 new\n", "{}", stderr(&out));
    let out = publish(
        &addr,
        "/a/stream/x",
        &["--id", "1", "--seq", "2", "--tcp"],
        second,
    );
    assert_eq!(stdout(&out), "1 new\n", "{}", stderr(&out));

    let mut r = BufReader::new(sub.stdout.take().unwrap());
    let (off, got) = read_record(&mut r);
    assert_eq!(off, 0, "header offset is the one pub printed");
    assert_eq!(got, first, "delivered body byte-exact over TCP");
    let (off, got) = read_record(&mut r);
    assert_eq!(off, 1);
    assert_eq!(got, second, "record boundary honoured over TCP");

    let _ = sub.kill();
    let _ = sub.wait();
}

/// A key file whose 64 BYTES contain a multibyte character used to panic on a
/// char boundary (exit 101 + backtrace); it is now a plain usage error (exit 2),
/// on every build (the hex is decoded before the transport is chosen).
#[test]
fn asb_rejects_a_multibyte_key_without_panicking() {
    let dir = std::env::temp_dir().join(format!(
        "asbkey_{}_{}",
        std::process::id(),
        CTR.fetch_add(1, Ordering::Relaxed)
    ));
    let _dir = Cleanup::new(&[&dir]);
    std::fs::create_dir_all(&dir).unwrap();
    let keyfile = dir.join("psk");
    let mut s = String::from("aé"); // 3 bytes
    s.push_str(&"a".repeat(61)); // 64 bytes, valid UTF-8, not hex
    assert_eq!(s.len(), 64);
    std::fs::write(&keyfile, s).unwrap();
    let out = asb()
        .args(["sub", "127.0.0.1:1", "/a/>", "--key-file"])
        .arg(&keyfile)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(2), "stderr: {}", stderr(&out));
    assert!(stderr(&out).contains("not valid hex"), "{}", stderr(&out));
    assert!(!stderr(&out).contains("panicked"), "{}", stderr(&out));

    // A sign is not hex either (`u8::from_str_radix` would have accepted `+f`).
    std::fs::write(&keyfile, "+f".repeat(32)).unwrap();
    let out = asb()
        .args(["sub", "127.0.0.1:1", "/a/>", "--key-file"])
        .arg(&keyfile)
        .stderr(Stdio::piped())
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(2));
    assert!(stderr(&out).contains("not valid hex"), "{}", stderr(&out));
}

/// The sealed transport from the shell: the PSK comes from a file (`--key-file`)
/// or an environment variable (`--key-env`) — never argv — and the roundtrip is
/// byte-exact through the XChaCha20-Poly1305 record layer. A wrong key is refused.
#[cfg(feature = "aead")]
#[test]
fn asb_sealed_tcp_roundtrip_with_key_from_env_and_file() {
    let (_tmp, log) = fresh_log("sealed");
    let dir = std::env::temp_dir().join(format!(
        "asbsealed_{}_{}",
        std::process::id(),
        CTR.fetch_add(1, Ordering::Relaxed)
    ));
    let _dir = Cleanup::new(&[&dir]);
    std::fs::create_dir_all(&dir).unwrap();
    let keyfile = dir.join("psk");
    let key_hex = "00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff";
    std::fs::write(&keyfile, format!("{key_hex}\n")).unwrap(); // trailing newline is fine
                                                               // 0600: `asb serve` refuses a key file anyone but its owner can read.
    std::fs::set_permissions(
        &keyfile,
        std::os::unix::fs::PermissionsExt::from_mode(0o600),
    )
    .unwrap();
    let keyfile = keyfile.to_str().unwrap().to_string();

    let (_s, addr) = serve(&log, &["--key-file", &keyfile]);

    let mut sub = asb()
        .args(["sub", &addr, "/a/stream/x", "--key-file", &keyfile])
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();

    let body: &[u8] = b"sealed\x00bytes\n";
    let mut c = asb()
        .args([
            "pub",
            &addr,
            "/a/stream/x",
            "--id",
            "1",
            "--seq",
            "1",
            "--key-env",
            "ASB_TEST_PSK",
        ])
        .env("ASB_TEST_PSK", key_hex)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    c.stdin.take().unwrap().write_all(body).unwrap();
    let out = c.wait_with_output().unwrap();
    assert_eq!(stdout(&out), "0 new\n", "{}", stderr(&out));

    let mut r = BufReader::new(sub.stdout.take().unwrap());
    assert_eq!(read_record(&mut r), (0, body.to_vec()));
    let _ = sub.kill();
    let _ = sub.wait();

    // The wrong key cannot publish (the broker drops the unauthenticated peer).
    let wrong = "ff".repeat(32);
    let mut c = asb()
        .args([
            "pub",
            &addr,
            "/a/stream/x",
            "--id",
            "1",
            "--seq",
            "2",
            "--key-env",
            "ASB_TEST_PSK",
        ])
        .env("ASB_TEST_PSK", &wrong)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    c.stdin.take().unwrap().write_all(b"x").unwrap();
    let out = c.wait_with_output().unwrap();
    assert_eq!(out.status.code(), Some(1), "wrong key: {}", stderr(&out));
    assert!(stdout(&out).is_empty());

    // An unset env var is a usage error, not an empty key.
    let out = asb()
        .args([
            "pub",
            &addr,
            "/a/stream/x",
            "--key-env",
            "ASB_TEST_PSK_UNSET",
        ])
        .env_remove("ASB_TEST_PSK_UNSET")
        .stdin(Stdio::null())
        .stderr(Stdio::piped())
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(2));
    assert!(
        stderr(&out).contains("--key-env ASB_TEST_PSK_UNSET"),
        "{}",
        stderr(&out)
    );
}
