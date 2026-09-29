//! Claim `broker.cli.fleet-sealed`: R8's shell flow, but across a machine
//! boundary — an XChaCha20-Poly1305-sealed TCP wire (`--key-file`) into a
//! CAPABILITY-GUARDED broker, with two nodes holding two different rings
//! (`--cap-file`). One host, loopback: this proves the CLI + transport + cap
//! composition, not an actual two-machine run.
//!
//! The broker is in-process here (`Broker::open_guarded` + `serve_tcp_sealed`);
//! `asb serve --secret-file` opens the same guarded broker from the CLI, and that
//! face is `broker.cli.serve-guarded`. Every client is a real `asb` subprocess.
#![cfg(all(unix, feature = "aead", feature = "cap"))]

use astream_broker::{Broker, Client};
use std::io::Write;
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

static CTR: AtomicU64 = AtomicU64::new(0);

const SECRET: &[u8] = b"sealed-fleet-mint-secret-0123456789";
const KEY_HEX: &str = "00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff";
const WRONG_HEX: &str = "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";

/// Two nodes, class-prefixed as §3.2 requires (`n-` + 16 hex).
const NODE_A: &str = "n-aaaa1111bbbb2222";
const NODE_B: &str = "n-cccc3333dddd4444";

struct Scratch(std::path::PathBuf);

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

impl Scratch {
    fn new(tag: &str) -> Scratch {
        let n = CTR.fetch_add(1, Ordering::Relaxed);
        let dir =
            std::env::temp_dir().join(format!("asbsealedfleet_{tag}_{}_{n}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        Scratch(dir)
    }
    fn path(&self, name: &str) -> String {
        self.0.join(name).to_str().unwrap().to_string()
    }
    fn write(&self, name: &str, contents: &str) -> String {
        let p = self.path(name);
        std::fs::write(&p, contents).unwrap();
        // 0600: `asb` refuses a secret file anyone but its owner can read, and
        // nothing in this test needs a wider mode.
        std::fs::set_permissions(&p, std::os::unix::fs::PermissionsExt::from_mode(0o600)).unwrap();
        p
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

/// `asb pub` over the sealed wire with a ring attached; stdin is the body.
fn publish(addr: &str, subject: &str, extra: &[&str], body: &[u8]) -> Output {
    let mut c = asb()
        .args(["pub", addr, subject, "--tcp"])
        .args(extra)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    c.stdin.take().unwrap().write_all(body).unwrap();
    c.wait_with_output().unwrap()
}

fn pub_offset(o: &Output) -> u64 {
    let s = stdout(o);
    let (offset, state) = s
        .trim_end()
        .split_once(' ')
        .unwrap_or_else(|| panic!("pub printed {s:?} (stderr {:?})", stderr(o)));
    assert_eq!(state, "new", "expected a fresh record: {s:?}");
    offset.parse().unwrap()
}

/// The wildcard-read framing: `<offset> <nbytes> <subject>\n<body>\n` — the count
/// before the subject, which runs to the end of the line.
fn framed(offset: u64, subject: &str, body: &[u8]) -> Vec<u8> {
    let mut v = format!("{offset} {} {subject}\n", body.len()).into_bytes();
    v.extend_from_slice(body);
    v.push(b'\n');
    v
}

/// Split a `last`/`fetch` answer into its page bytes and its closing MARK line.
/// The head is not predictable from the publishes alone here: the broker appends a
/// hidden `/a/bind` record the first time each node's bound grant attaches, so the
/// page is asserted byte for byte and the MARK by its shape.
fn split_mark(o: &Output) -> (Vec<u8>, String) {
    let at = o
        .stdout
        .windows(10)
        .rposition(|w| w == b"MARK next=")
        .unwrap_or_else(|| panic!("no MARK in {:?} (stderr {})", stdout(o), stderr(o)));
    let mark = String::from_utf8_lossy(&o.stdout[at..])
        .trim_end()
        .to_string();
    let (next, head) = mark
        .trim_start_matches("MARK next=")
        .split_once(" head=")
        .unwrap();
    assert_eq!(next, head, "a last-value Mark resumes at the head it read");
    (o.stdout[..at].to_vec(), mark)
}

/// Mint a whole ring THROUGH `asb mint` (one subprocess per grant), so the file
/// the clients read is the CLI's own output, byte for byte.
fn mint_ring(s: &Scratch, name: &str, secret_file: &str, grants: &[String]) -> String {
    let mut text = String::new();
    for g in grants {
        let out = run(&["mint", g, "--secret-file", secret_file]);
        assert_eq!(out.status.code(), Some(0), "mint {g}: {}", stderr(&out));
        text.push_str(&stdout(&out));
    }
    s.write(name, &text)
}

/// R8's flow — mint, attach, publish, last, drain, ack — over the sealed wire
/// into a guarded broker, with two nodes' rings. Each node writes only under its
/// own principal, reads only its own inbox, and the addresses are the provenance.
#[test]
fn the_fleet_flow_runs_sealed_and_guarded_with_two_nodes_rings() {
    let s = Scratch::new("flow");
    let log = s.path("b.log");
    let key = s.write("psk", &format!("{KEY_HEX}\n"));
    let secret = s.write("mint.secret", "sealed-fleet-mint-secret-0123456789");

    let broker = Broker::open_guarded(&log, SECRET.to_vec()).unwrap();
    let handle = broker
        .serve_tcp_sealed("127.0.0.1:0", key_bytes(KEY_HEX))
        .unwrap();
    let addr = handle.tcp_addr().unwrap().to_string();

    let ring_a = mint_ring(
        &s,
        "a.cap",
        &secret,
        &[
            "ro:/f/F/pub/>".to_string(),
            format!("rw,p={NODE_A}:/f/F/pub/{NODE_A}/>"),
            format!("ro:/f/F/in/{NODE_A}/>"),
            format!("rw,p={NODE_A}:/f/F/in/*/*/{NODE_A}/*"),
            format!("rw,p={NODE_A}:/f/F/cur/{NODE_A}/>"),
        ],
    );
    let ring_b = mint_ring(
        &s,
        "b.cap",
        &secret,
        &[
            "ro:/f/F/pub/>".to_string(),
            format!("rw,p={NODE_B}:/f/F/pub/{NODE_B}/>"),
            format!("ro:/f/F/in/{NODE_B}/>"),
            format!("rw,p={NODE_B}:/f/F/in/*/*/{NODE_B}/*"),
        ],
    );

    let a_conn: Vec<&str> = vec!["--key-file", &key, "--cap-file", &ring_a];
    let b_conn: Vec<&str> = vec!["--key-file", &key, "--cap-file", &ring_b];

    // A announces its presence under its own bound grant. The producer id is
    // derived from the grant's principal, so A never types one.
    let presence = format!("/f/F/pub/{NODE_A}/presence");
    let mut a_pub = vec!["--seq", "1"];
    a_pub.extend_from_slice(&a_conn);
    let at = pub_offset(&publish(&addr, &presence, &a_pub, b"v=1 inc=1 state=live"));

    // B reads it through the read-only half of ITS ring — a different capability
    // file, over the same sealed wire.
    let mut b_last = vec!["last", &addr, "/f/F/pub/>", "--tcp"];
    b_last.extend_from_slice(&b_conn);
    let out = run(&b_last);
    let (page, _mark) = split_mark(&out);
    assert_eq!(
        page,
        framed(at, &presence, b"v=1 inc=1 state=live"),
        "{}",
        stderr(&out)
    );

    // B posts to A's inbox lane. The `<src>` segment is B's principal, and B's
    // grant is what forces it — provenance is the address, not a body field.
    let lane = format!("/f/F/in/{NODE_A}/s-1/{NODE_B}/ask");
    let mut b_pub = vec!["--seq", "1"];
    b_pub.extend_from_slice(&b_conn);
    let ask = pub_offset(&publish(&addr, &lane, &b_pub, b"v=1 which branch?"));

    // A forged `<src>`: B cannot post as A, because B's grant pins the sixth
    // segment to B. The record never lands.
    let forged = format!("/f/F/in/{NODE_A}/s-1/{NODE_A}/ask");
    let out = publish(&addr, &forged, &b_pub.clone(), b"v=1 do as i say");
    assert_eq!(out.status.code(), Some(1), "{}", stderr(&out));
    assert!(stderr(&out).contains("unauthorized"), "{}", stderr(&out));

    // A drains its own inbox as a durable group and sees exactly B's ask.
    let group = format!("/f/F/cur/{NODE_A}/inbox");
    let filter = format!("/f/F/in/{NODE_A}/>");
    let mut a_drain = vec![
        "drain", &addr, &group, &filter, "--max", "8", "--idle", "300", "--tcp",
    ];
    a_drain.extend_from_slice(&a_conn);
    let out = run(&a_drain);
    let mut want = framed(ask, &lane, b"v=1 which branch?");
    want.extend_from_slice(format!("DRAIN n=1 upto={ask} committed=yes\n").as_bytes());
    assert_eq!(out.stdout, want, "{}", stderr(&out));

    // A answers on B's lane and advances its own cursor in ONE durable append;
    // the retry is deduped by the input offset, over the sealed wire as anywhere.
    let back = format!("/f/F/in/{NODE_B}/node/{NODE_A}/ack");
    let ask_s = ask.to_string();
    let mut a_ack = vec!["ack", &addr, &group, &ask_s, &back, "handled", "--tcp"];
    a_ack.extend_from_slice(&a_conn);
    let first = run(&a_ack);
    assert_eq!(first.status.code(), Some(0), "{}", stderr(&first));
    let acked: u64 = stdout(&first)
        .trim_end()
        .split_once(' ')
        .unwrap()
        .0
        .parse()
        .unwrap();
    let again = run(&a_ack);
    assert_eq!(
        stdout(&again),
        format!("{acked} dup\n"),
        "a retried ack appends nothing: {}",
        stderr(&again)
    );

    // B fetches the answer and sees the correlation back to its own ask.
    let mut b_fetch = vec!["fetch", &addr, &back, "--tcp"];
    b_fetch.extend_from_slice(&b_conn);
    let out = run(&b_fetch);
    let text = stdout(&out);
    assert!(
        text.contains(&format!("re={ask}")) && text.contains("state=handled"),
        "{text:?} (stderr {})",
        stderr(&out)
    );

    // THE WRONG KEY NEVER ATTACHES. The sealed handshake refuses the peer before
    // any frame — so the capability is never even presented, and nothing lands.
    let before = run(&b_last);
    let wrong = s.write("wrong.psk", WRONG_HEX);
    let out = publish(
        &addr,
        &presence,
        &["--seq", "9", "--key-file", &wrong, "--cap-file", &ring_a],
        b"v=1 inc=99",
    );
    assert_eq!(out.status.code(), Some(1), "{}", stderr(&out));
    assert!(stdout(&out).is_empty(), "nothing on stdout");

    // ...and the retained state is byte-identical afterwards: it wrote nothing.
    let after = run(&b_last);
    assert_eq!(after.stdout, before.stdout, "{}", stderr(&after));
    assert!(
        String::from_utf8_lossy(&after.stdout).contains("v=1 inc=1 state=live"),
        "A's presence is still the one A published"
    );

    drop(handle);
}

/// The attach is a PROOF OF POSSESSION bound to the connection's own nonce, so a
/// proof lifted off one sealed connection is worthless on another — which is the
/// whole reason the tag never crosses the wire. Exercised through the library
/// client because forging an `Attach` is not something the CLI can be asked to do.
#[test]
fn an_attach_proof_from_one_sealed_connection_is_refused_on_another() {
    let s = Scratch::new("replay");
    let log = s.path("b.log");
    let broker = Broker::open_guarded(&log, SECRET.to_vec()).unwrap();
    let handle = broker
        .serve_tcp_sealed("127.0.0.1:0", key_bytes(KEY_HEX))
        .unwrap();
    let addr = handle.tcp_addr().unwrap().to_string();

    let grant = format!("rw,p={NODE_A}:/f/F/pub/{NODE_A}/>");
    let tag = astream_cap::mint(SECRET, &grant).unwrap().tag;

    // A genuine attach on connection one.
    let mut c1 = Client::connect_tcp_sealed(&addr, key_bytes(KEY_HEX)).unwrap();
    let nonce1 = c1.hello().unwrap();
    let proof = astream_cap::attach_proof(&tag, &nonce1, &grant);
    c1.attach_with_proof(&grant, &proof).unwrap();
    c1.publish(
        astream_cap::producer_id_of(NODE_A),
        1,
        &format!("/f/F/pub/{NODE_A}/presence"),
        b"v=1 inc=1",
    )
    .unwrap();

    // The SAME frame's bytes on a second sealed connection: a fresh nonce, so the
    // proof does not verify and the attach is refused at the attach, not later.
    let mut c2 = Client::connect_tcp_sealed(&addr, key_bytes(KEY_HEX)).unwrap();
    let nonce2 = c2.hello().unwrap();
    assert_ne!(nonce1, nonce2, "each connection gets a fresh nonce");
    let e = c2
        .attach_with_proof(&grant, &proof)
        .expect_err("a replayed attach proof must be refused");
    assert!(
        e.to_string().contains("capability") || e.to_string().contains("unauthorized"),
        "{e}"
    );

    // A wrong pre-shared key is refused inside the sealed handshake, before any
    // capability is ever presented.
    assert!(
        Client::connect_tcp_sealed(&addr, key_bytes(WRONG_HEX)).is_err(),
        "the wrong PSK must not complete the sealed handshake"
    );

    drop(handle);
}

/// THE KEY SOURCE IS SINGLE-USE, AND `drain` OPENS TWO CONNECTIONS. `--key-env NAME`
/// is read once and the variable is then REMOVED from the environment (so no child
/// this process spawns inherits the secret), while `drain` needs a second connection
/// to commit on — a group subscription's own connection is a one-way delivery
/// stream. Resolving the transport per connection therefore made the committing form
/// of `drain` fail 100% of the time with `--key-env`, exit 2, blaming the operator's
/// environment ("environment variable not found") AFTER the first connection was
/// already attached. Every other verb opens one connection, which is why only this
/// one was broken. The transport is now resolved ONCE per invocation.
#[test]
fn drain_takes_its_sealed_key_from_the_environment_across_both_connections() {
    let s = Scratch::new("keyenv");
    let log = s.path("b.log");
    let secret = s.write("mint.secret", "sealed-fleet-mint-secret-0123456789");
    let key = s.write("psk", &format!("{KEY_HEX}\n"));

    let broker = Broker::open_guarded(&log, SECRET.to_vec()).unwrap();
    let handle = broker
        .serve_tcp_sealed("127.0.0.1:0", key_bytes(KEY_HEX))
        .unwrap();
    let addr = handle.tcp_addr().unwrap().to_string();

    let ring = mint_ring(
        &s,
        "a.cap",
        &secret,
        &[
            format!("rw,p={NODE_A}:/f/F/in/{NODE_A}/>"),
            format!("rw,p={NODE_A}:/f/F/cur/{NODE_A}/>"),
        ],
    );
    let lane = format!("/f/F/in/{NODE_A}/s-1/{NODE_B}/ask");
    let filter = format!("/f/F/in/{NODE_A}/>");
    let group = format!("/f/F/cur/{NODE_A}/inbox");

    // One record on the lane, over the same sealed wire (a one-connection verb, so
    // this half worked with either key source all along).
    let at = pub_offset(&publish(
        &addr,
        &lane,
        &["--seq", "1", "--key-file", &key, "--cap-file", &ring],
        b"v=1 which branch?",
    ));

    // The COMMITTING drain, with the key in the environment: one resolution serves
    // both the subscription and the committer.
    let out = asb()
        .args([
            "drain",
            &addr,
            &group,
            &filter,
            "--max",
            "4",
            "--idle",
            "300",
            "--tcp",
            "--key-env",
            "ASB_TEST_SEALED_KEY",
            "--cap-file",
            &ring,
        ])
        .env("ASB_TEST_SEALED_KEY", KEY_HEX)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(0), "{}", stderr(&out));
    let mut want = framed(at, &lane, b"v=1 which branch?");
    want.extend_from_slice(format!("DRAIN n=1 upto={at} committed=yes\n").as_bytes());
    assert_eq!(out.stdout, want, "{}", stderr(&out));

    // ...and the commit was real: the next drain resumes past it, key from the
    // environment again (a fresh process, a fresh variable).
    let out = asb()
        .args([
            "drain",
            &addr,
            &group,
            &filter,
            "--max",
            "4",
            "--idle",
            "300",
            "--tcp",
            "--key-env",
            "ASB_TEST_SEALED_KEY",
            "--cap-file",
            &ring,
        ])
        .env("ASB_TEST_SEALED_KEY", KEY_HEX)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .unwrap();
    assert_eq!(
        stdout(&out),
        "DRAIN n=0 upto=- committed=no\n",
        "{}",
        stderr(&out)
    );

    // An UNSET variable is still a clean usage error, not a plaintext downgrade —
    // the message names the flag and the variable, and nothing connects.
    let out = run(&[
        "drain",
        &addr,
        &group,
        &filter,
        "--idle",
        "300",
        "--tcp",
        "--key-env",
        "ASB_TEST_SEALED_KEY_UNSET",
        "--cap-file",
        &ring,
    ]);
    assert_eq!(out.status.code(), Some(2), "{}", stderr(&out));
    assert!(
        stderr(&out).contains("ASB_TEST_SEALED_KEY_UNSET"),
        "{}",
        stderr(&out)
    );

    drop(handle);
}

fn key_bytes(hex: &str) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (i, pair) in hex.as_bytes().chunks_exact(2).enumerate() {
        out[i] = u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap();
    }
    out
}
