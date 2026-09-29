//! Claim `broker.cli.serve-guarded`: `asb serve` opens a GUARDED broker from the
//! command line, and holds its listeners and secret files to the rules the aterm
//! fabric's broker verb already enforced.
//!
//! Before this, a guarded broker could only be opened by an embedder
//! (`Broker::open_guarded`): `asb mint` sealed capabilities for a guard the
//! generic CLI could not start, so every CLI-run broker checked nothing on attach.
//! Everything here is a real `asb` subprocess, synchronized on the serve readiness
//! lines — no sleeps.
#![cfg(unix)]

use std::io::{BufRead, BufReader};
use std::process::{Child, ChildStdout, Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

static CTR: AtomicU64 = AtomicU64::new(0);

/// A mint secret comfortably over the 32-byte floor.
#[cfg(feature = "cap")]
const SECRET: &str = "serve-guarded-mint-secret-0123456789abcdef";
/// A second, unrelated secret: capabilities minted under it must not attach.
#[cfg(feature = "cap")]
const OTHER_SECRET: &str = "some-other-fleets-mint-secret-0123456789";

struct Paths {
    dir: std::path::PathBuf,
}

fn fresh(tag: &str) -> Paths {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let dir = std::env::temp_dir().join(format!("asbguard_{tag}_{pid}_{n}"));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    Paths { dir }
}

impl Drop for Paths {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

impl Paths {
    fn path(&self, name: &str) -> String {
        self.dir.join(name).to_str().unwrap().to_string()
    }

    /// Write `contents` at `name` with `mode`; returns the path.
    fn file_mode(&self, name: &str, contents: &[u8], mode: u32) -> String {
        let p = self.path(name);
        std::fs::write(&p, contents).unwrap();
        std::fs::set_permissions(&p, std::os::unix::fs::PermissionsExt::from_mode(mode)).unwrap();
        p
    }

    /// A private (0600) file.
    fn file(&self, name: &str, contents: &[u8]) -> String {
        self.file_mode(name, contents, 0o600)
    }

    fn exists(&self, name: &str) -> bool {
        self.dir.join(name).exists()
    }
}

fn asb() -> Command {
    Command::new(env!("CARGO_BIN_EXE_asb"))
}

fn run(args: &[&str]) -> Output {
    asb()
        .args(args)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .unwrap()
}

fn stdout(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).into_owned()
}
fn stderr(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

/// Assert a usage error: exit 2, the reason on stderr, nothing on stdout.
fn refused(args: &[&str], want: &str) {
    let out = run(args);
    assert_eq!(out.status.code(), Some(2), "{args:?}: {}", stderr(&out));
    assert!(
        stderr(&out).contains(want),
        "{args:?}: stderr {:?} should mention {want:?}",
        stderr(&out)
    );
    assert!(stdout(&out).is_empty(), "{args:?}: nothing on stdout");
}

/// A serving broker; killed + reaped on drop.
struct Serve(Child);

impl Drop for Serve {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

/// `asb serve <args>`, synchronized on its readiness line(s): returns the broker
/// and every `listening <x>` value, in order.
fn serve(args: &[&str], lines: usize) -> (Serve, Vec<String>) {
    let mut child = asb()
        .arg("serve")
        .args(args)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let mut r: BufReader<ChildStdout> = BufReader::new(child.stdout.take().unwrap());
    let mut bound = Vec::new();
    for _ in 0..lines {
        let mut line = String::new();
        r.read_line(&mut line).unwrap();
        let Some(rest) = line.strip_prefix("listening ") else {
            let _ = child.kill();
            let out = child.wait_with_output().unwrap();
            panic!("serve {args:?}: {line:?} (stderr {:?})", stderr(&out));
        };
        bound.push(rest.trim_end().to_string());
    }
    (Serve(child), bound)
}

/// `asb pub <ep> <subject> <extra…>` with stdin = body.
#[cfg(feature = "cap")]
fn publish(ep: &str, subject: &str, extra: &[&str], body: &[u8]) -> Output {
    let mut c = asb()
        .args(["pub", ep, subject])
        .args(extra)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    std::io::Write::write_all(&mut c.stdin.take().unwrap(), body).unwrap();
    c.wait_with_output().unwrap()
}

/// The offset an `asb pub` printed as `<offset> new`.
#[cfg(feature = "cap")]
fn pub_offset(o: &Output) -> u64 {
    let s = stdout(o);
    let (offset, state) = s.trim_end().split_once(' ').unwrap_or_else(|| {
        panic!("pub printed {s:?} (stderr {:?})", stderr(o));
    });
    assert_eq!(state, "new", "expected a fresh record: {s:?}");
    offset.parse().unwrap()
}

/// `<offset> <nbytes> <subject>\n<body>\n` — the `fetch` row framing.
#[cfg(feature = "cap")]
fn framed(offset: u64, subject: &str, body: &[u8]) -> Vec<u8> {
    let mut v = format!("{offset} {} {subject}\n", body.len()).into_bytes();
    v.extend_from_slice(body);
    v.push(b'\n');
    v
}

#[cfg(feature = "cap")]
fn contains(hay: &[u8], needle: &[u8]) -> bool {
    hay.windows(needle.len()).any(|w| w == needle)
}

/// `asb mint <grant> --secret-file <secret>` into a cap file named `name`.
#[cfg(feature = "cap")]
fn mint_ring(p: &Paths, name: &str, secret_file: &str, grant: &str) -> String {
    let out = run(&["mint", grant, "--secret-file", secret_file]);
    assert_eq!(out.status.code(), Some(0), "mint: {}", stderr(&out));
    p.file(name, &out.stdout)
}

/// THE GUARD, PROVEN PRESENT RATHER THAN ASSUMED: the same three publishes against
/// a guarded and an unguarded CLI broker. Guarded, only the capability minted
/// under the broker's own secret attaches; a capability minted under another
/// secret, and no capability at all, are refused inside the attach and nothing
/// lands. Unguarded, the capability-less publish lands — which is the difference
/// the secret makes.
#[cfg(feature = "cap")]
#[test]
fn a_guarded_serve_admits_only_capabilities_minted_under_its_secret() {
    let p = fresh("guard");
    let secret = p.file("mint.secret", SECRET.as_bytes());
    let other = p.file("other.secret", OTHER_SECRET.as_bytes());
    let sock = p.path("b.sock");
    let log = p.path("b.log");
    let (_b, bound) = serve(&[&sock, &log, "--secret-file", &secret], 1);
    assert_eq!(bound, std::slice::from_ref(&sock));

    let grant = "rw,p=n-one:/f/F/pub/n1/>";
    let good = mint_ring(&p, "good.cap", &secret, grant);
    let forged = mint_ring(&p, "forged.cap", &other, grant);
    let subject = "/f/F/pub/n1/row";

    let ok = publish(&sock, subject, &["--cap-file", &good], b"minted-here");
    let at = pub_offset(&ok);

    let bad = publish(
        &sock,
        subject,
        &["--cap-file", &forged],
        b"minted-elsewhere",
    );
    assert_eq!(bad.status.code(), Some(1), "forged: {}", stderr(&bad));
    assert!(
        stdout(&bad).is_empty(),
        "a refused attach publishes nothing"
    );

    let bare = publish(&sock, subject, &["--id", "7"], b"no-capability");
    assert_eq!(bare.status.code(), Some(1), "bare: {}", stderr(&bare));
    assert!(
        stdout(&bare).is_empty(),
        "a refused attach publishes nothing"
    );

    // Exactly one record is on the lane: the one the genuine capability sent.
    let f = run(&["fetch", &sock, "/f/F/pub/n1/>", "--cap-file", &good]);
    assert_eq!(f.status.code(), Some(0), "fetch: {}", stderr(&f));
    assert!(contains(&f.stdout, &framed(at, subject, b"minted-here")));
    assert!(!contains(&f.stdout, b"minted-elsewhere"));
    assert!(!contains(&f.stdout, b"no-capability"));

    // The same capability-less publish against an UNGUARDED CLI broker lands.
    let sock2 = p.path("open.sock");
    let log2 = p.path("open.log");
    let (_open, _) = serve(&[&sock2, &log2], 1);
    let landed = publish(&sock2, subject, &["--id", "7"], b"no-capability");
    pub_offset(&landed);
}

/// The secret may come from the ENVIRONMENT too (trimmed: it is text), and a
/// capability `mint` sealed from the same secret stored in a file attaches to it:
/// `mint` and `serve` read the secret through one function, so they cannot disagree
/// about its bytes. A FILE is its bytes exactly, so the same text with a trailing
/// newline is a different secret, and its capability is refused.
#[cfg(feature = "cap")]
#[test]
fn a_secret_from_the_environment_guards_the_same_way() {
    let p = fresh("env");
    let secret = p.file("mint.secret", SECRET.as_bytes());
    let echoed = p.file("echoed.secret", format!("{SECRET}\n").as_bytes());
    let sock = p.path("b.sock");
    let log = p.path("b.log");
    let mut child = asb()
        .args([
            "serve",
            &sock,
            &log,
            "--secret-env",
            "ASB_TEST_SERVE_SECRET",
        ])
        .env("ASB_TEST_SERVE_SECRET", SECRET)
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    let mut line = String::new();
    BufReader::new(child.stdout.take().unwrap())
        .read_line(&mut line)
        .unwrap();
    let _b = Serve(child);
    assert_eq!(line, format!("listening {sock}\n"));

    let ring = mint_ring(&p, "ring.cap", &secret, "rw,p=n-two:/f/F/pub/n2/>");
    pub_offset(&publish(
        &sock,
        "/f/F/pub/n2/x",
        &["--cap-file", &ring],
        b"b",
    ));
    let other = mint_ring(&p, "echoed.cap", &echoed, "rw,p=n-two:/f/F/pub/n2/>");
    let wrong = publish(&sock, "/f/F/pub/n2/x", &["--cap-file", &other], b"b");
    assert_eq!(
        wrong.status.code(),
        Some(1),
        "an echoed newline is a different secret"
    );
    let bare = publish(&sock, "/f/F/pub/n2/x", &["--id", "3"], b"b");
    assert_eq!(bare.status.code(), Some(1), "{}", stderr(&bare));
}

/// A SECRET THE BROKER CANNOT TRUST IS REFUSED BEFORE THE LOG IS OPENED: a file
/// others can read, one under the 32-byte floor, and one that only falls under it
/// once its surrounding whitespace is trimmed (which the message names, because a
/// byte-for-byte reader of the same file would seal with every byte). Each is a
/// usage error, and none leaves a log behind. `mint` holds its secret to the same
/// rules.
#[cfg(feature = "cap")]
#[test]
fn serve_and_mint_refuse_a_secret_they_cannot_trust() {
    let p = fresh("badsecret");
    let sock = p.path("b.sock");
    let log = p.path("b.log");

    let loose = p.file_mode("loose.secret", SECRET.as_bytes(), 0o644);
    refused(
        &["serve", &sock, &log, "--secret-file", &loose],
        "chmod 600",
    );
    refused(&["mint", "ro:/f/F/>", "--secret-file", &loose], "chmod 600");

    let short = p.file("short.secret", b"only-twenty-bytes-xx");
    refused(
        &["serve", &sock, &log, "--secret-file", &short],
        "at least 32",
    );
    refused(
        &["mint", "ro:/f/F/>", "--secret-file", &short],
        "at least 32",
    );

    // A RAW secret that ends in a whitespace byte — what `head -c 32 /dev/urandom`
    // writes about one time in twenty-five — is used BYTE FOR BYTE: `mint` seals with
    // all 32 bytes, exactly as a broker that `fs::read`s the same file verifies.
    let mut raw = vec![b'k'; 31];
    raw.push(b' ');
    let edge = p.file("edge.secret", &raw);
    let out = run(&["mint", "ro:/f/F/>", "--secret-file", &edge]);
    assert_eq!(out.status.code(), Some(0), "{}", stderr(&out));
    let want = astream_cap::capfile::format_line(
        "ro:/f/F/>",
        &astream_cap::mint(&raw, "ro:/f/F/>").unwrap().tag,
    );
    assert_eq!(stdout(&out).trim_end(), want, "the file's 32 bytes, not 31");

    let fine = p.file("fine.secret", SECRET.as_bytes());
    refused(
        &[
            "serve",
            &sock,
            &log,
            "--secret-file",
            &fine,
            "--secret-env",
            "X",
        ],
        "mutually exclusive",
    );
    refused(
        &[
            "serve",
            &sock,
            &log,
            "--secret-env",
            "ASB_TEST_SURELY_UNSET_VARIABLE",
        ],
        "ASB_TEST_SURELY_UNSET_VARIABLE",
    );
    assert!(!p.exists("b.log"), "no refusal may leave a log behind");
}

/// A build without `cap` cannot verify a capability, so it cannot guard: the
/// secret is refused BY NAME rather than accepted and silently not enforced.
#[cfg(not(feature = "cap"))]
#[test]
fn a_build_without_cap_refuses_to_pretend_to_guard() {
    let p = fresh("nocap");
    let secret = p.file("mint.secret", b"serve-guarded-mint-secret-0123456789abcdef");
    refused(
        &[
            "serve",
            &p.path("b.sock"),
            &p.path("b.log"),
            "--secret-file",
            &secret,
        ],
        "--features cap",
    );
    assert!(!p.exists("b.log"));
}

/// A TCP LISTENER BINDS LOOPBACK UNLESS TOLD OTHERWISE, and the two new flags
/// exist only where they mean something. Every refusal here happens before the
/// log is opened.
#[test]
fn tcp_binds_loopback_unless_allowed_and_the_listener_flags_need_tcp() {
    let p = fresh("flags");
    let sock = p.path("b.sock");
    let log = p.path("b.log");
    refused(
        &["serve", &sock, &log, "--unix", &p.path("x.sock")],
        "--unix needs a TCP listener",
    );
    refused(
        &["serve", &sock, &log, "--allow-remote"],
        "--allow-remote applies to a TCP listener",
    );
    refused(
        &["serve", "0.0.0.0:0", &log, "--tcp"],
        "is not a loopback address",
    );
    refused(
        &["serve", "[::]:0", &log, "--tcp"],
        "is not a loopback address",
    );
    // A key implies TCP, so the sealed listener is held to the same rule — and a
    // key file others can read is refused before the key is even parsed.
    let key = p.file("k.key", format!("{}\n", "ab".repeat(32)).as_bytes());
    refused(
        &["serve", "0.0.0.0:0", &log, "--key-file", &key],
        "is not a loopback address",
    );
    let loose_key = p.file_mode(
        "loose.key",
        format!("{}\n", "ab".repeat(32)).as_bytes(),
        0o640,
    );
    refused(
        &["serve", "127.0.0.1:0", &log, "--key-file", &loose_key],
        "chmod 600",
    );
    assert!(!p.exists("b.log"), "no refusal may leave a log behind");

    // Loopback by name still binds.
    let (_b, bound) = serve(&["localhost:0", &log, "--tcp"], 1);
    assert!(bound[0].contains(':'), "{bound:?}");
}

/// A REFUSED BIND LEAVES NO EMPTY LOG BEHIND — but only a log this invocation
/// created: an existing one is never touched.
#[test]
fn a_refused_bind_removes_only_the_log_it_created() {
    let p = fresh("bind");
    let taken = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
    let ep = taken.local_addr().unwrap().to_string();

    let out = run(&["serve", &ep, &p.path("new.log"), "--tcp"]);
    assert_eq!(out.status.code(), Some(1), "{}", stderr(&out));
    assert!(stdout(&out).is_empty());
    assert!(
        !p.exists("new.log"),
        "the log this call created is gone again"
    );

    let kept = p.file("kept.log", b"");
    let out = run(&["serve", &ep, &kept, "--tcp"]);
    assert_eq!(out.status.code(), Some(1), "{}", stderr(&out));
    assert!(
        p.exists("kept.log"),
        "a log that existed before is never removed"
    );
}

/// ONE BROKER, ONE LOG, ONE GUARD, TWO ACCEPTORS: a sealed TCP listener with a
/// Unix socket beside it. A record published on the socket is fetched over the
/// sealed wire at the same offset; the guard holds on the socket as well as on
/// the port; and a peer without the pre-shared key never reaches the attach.
#[cfg(all(feature = "cap", feature = "aead"))]
#[test]
fn a_sealed_listener_serves_a_unix_socket_beside_it_from_one_guarded_broker() {
    let p = fresh("beside");
    let secret = p.file("mint.secret", SECRET.as_bytes());
    let key = p.file("k.key", format!("{}\n", "5a".repeat(32)).as_bytes());
    let wrong = p.file("wrong.key", format!("{}\n", "a5".repeat(32)).as_bytes());
    let sock = p.path("b.sock");
    let log = p.path("b.log");
    let (_b, bound) = serve(
        &[
            "127.0.0.1:0",
            &log,
            "--key-file",
            &key,
            "--secret-file",
            &secret,
            "--unix",
            &sock,
        ],
        2,
    );
    let addr = bound[0].clone();
    assert_eq!(bound[1], sock, "the second readiness line names the socket");

    let ring = mint_ring(&p, "ring.cap", &secret, "rw,p=n-three:/f/F/pub/n3/>");
    let subject = "/f/F/pub/n3/row";
    let at = pub_offset(&publish(
        &sock,
        subject,
        &["--cap-file", &ring],
        b"over-the-socket",
    ));

    let f = run(&[
        "fetch",
        &addr,
        "/f/F/pub/n3/>",
        "--key-file",
        &key,
        "--cap-file",
        &ring,
    ]);
    assert_eq!(f.status.code(), Some(0), "sealed fetch: {}", stderr(&f));
    assert!(contains(
        &f.stdout,
        &framed(at, subject, b"over-the-socket")
    ));

    let bare = publish(&sock, subject, &["--id", "9"], b"unguarded?");
    assert_eq!(
        bare.status.code(),
        Some(1),
        "the socket is guarded too: {}",
        stderr(&bare)
    );

    let keyless = publish(
        &addr,
        subject,
        &["--key-file", &wrong, "--cap-file", &ring],
        b"x",
    );
    assert_eq!(keyless.status.code(), Some(1), "{}", stderr(&keyless));
    assert!(stdout(&keyless).is_empty());
}
