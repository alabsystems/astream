//! Capability enforcement on the paths a single per-request check does not cover.
//!
//! - A subscription is ONE request that then streams for as long as the connection
//!   lives, so authorizing it once at subscribe time let it outlive the capability
//!   that authorized it. It must end, with an error that says why, at the deadline.
//! - A guarded broker whose secret is EMPTY guards nothing: HMAC under an empty key
//!   is computable by anyone, so anyone can mint any capability. It must not open.

#![cfg(all(unix, feature = "cap"))]

use astream_broker::{broker_refusal, Broker, BrokerHandle, BrokerRefusal, Client};
use astream_cap::mint;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

static CTR: AtomicU64 = AtomicU64::new(0);
const SECRET: &[u8] = b"core-cap-hardening";

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

fn paths() -> (Cleanup, String, String) {
    let n = CTR.fetch_add(1, Ordering::Relaxed);
    let pid = std::process::id();
    let log = format!("/tmp/ascore_cap_{pid}_{n}.log");
    let _ = std::fs::remove_file(&log);
    let sock = format!("/tmp/ascore_cap_{pid}_{n}.sock");
    (Cleanup::new(&[&log, &sock]), log, sock)
}

fn fresh() -> (Cleanup, Broker, BrokerHandle, String) {
    let (tmp, log, sock) = paths();
    let broker = Broker::open_guarded(&log, SECRET.to_vec()).unwrap();
    let handle = broker.serve(&sock).unwrap();
    (tmp, broker, handle, sock)
}

fn now_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| d.as_millis() as u64)
}

/// A writer holding a non-expiring capability for the whole tree.
fn writer(sock: &str) -> Client {
    let god = mint(SECRET, "rw:/>").unwrap();
    let mut w = Client::connect(sock).unwrap();
    w.attach(&god.filter, &god.tag).unwrap();
    w
}

/// A subscription under traffic stops delivering once its capability expires: every
/// record is either delivered before the deadline or refused with `expired`.
#[test]
fn a_streaming_subscription_ends_when_its_capability_expires() {
    let (_tmp, _b, mut h, sock) = fresh();
    let mut w = writer(&sock);
    let soon = now_ms() + 400;
    let cap = mint(SECRET, &format!("ro,exp={soon}:/a/s/>")).unwrap();
    let mut r = Client::connect(&sock).unwrap();
    r.attach(&cap.filter, &cap.tag).unwrap();
    let mut sub = r.subscribe(0, "/a/s/>").unwrap();

    w.publish(1, 0, "/a/s/x", b"before").unwrap();
    assert_eq!(sub.recv().unwrap().unwrap().2, b"before");

    let bound = now_ms() + 10_000;
    let mut seq = 1u64;
    let refusal = loop {
        w.publish(1, seq, "/a/s/x", b"more").unwrap();
        seq += 1;
        match sub.recv() {
            Ok(Some(_)) => assert!(
                now_ms() < bound,
                "the capability expired at {soon} and the subscription still delivers"
            ),
            Ok(None) => panic!("the subscription ended without saying why"),
            Err(e) => break e,
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    assert!(
        broker_refusal(&refusal).is_some_and(BrokerRefusal::is_expired),
        "a stream ended at its deadline must read as expired: {refusal}"
    );
    assert!(now_ms() >= soon, "refused before its deadline");
    drop(sub);
    h.shutdown();
}

/// A PARKED subscription (no traffic) ends at the deadline too, not whenever the
/// next matching record happens to arrive.
#[test]
fn a_parked_subscription_ends_at_its_capabilitys_expiry() {
    let (_tmp, _b, mut h, sock) = fresh();
    let soon = now_ms() + 300;
    let cap = mint(SECRET, &format!("ro,exp={soon}:/a/s/>")).unwrap();
    let mut r = Client::connect(&sock).unwrap();
    r.attach(&cap.filter, &cap.tag).unwrap();
    let mut sub = r.subscribe(0, "/a/s/>").unwrap();
    sub.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
    let err = sub
        .recv()
        .expect_err("a subscription with nothing to deliver outlived its capability");
    assert!(
        broker_refusal(&err).is_some_and(BrokerRefusal::is_expired),
        "a parked stream ended at its deadline must read as expired: {err}"
    );
    assert!(now_ms() >= soon, "refused before its deadline");
    drop(sub);
    h.shutdown();
}

/// A capability with no expiry keeps its subscription open indefinitely, and a
/// subscription authorized by SEVERAL grants lasts as long as the latest of them.
#[test]
fn a_subscription_lasts_as_long_as_the_latest_grant_that_authorizes_it() {
    let (_tmp, _b, mut h, sock) = fresh();
    let mut w = writer(&sock);
    let short = mint(SECRET, &format!("ro,exp={}:/a/s/>", now_ms() + 200)).unwrap();
    let long = mint(SECRET, "ro:/a/>").unwrap();
    let mut r = Client::connect(&sock).unwrap();
    r.attach(&short.filter, &short.tag).unwrap();
    r.attach(&long.filter, &long.tag).unwrap();
    let mut sub = r.subscribe(0, "/a/s/>").unwrap();
    std::thread::sleep(Duration::from_millis(500)); // past the short grant's deadline
    w.publish(1, 0, "/a/s/x", b"still").unwrap();
    assert_eq!(sub.recv().unwrap().unwrap().2, b"still");
    drop(sub);
    h.shutdown();
}

#[test]
fn open_guarded_refuses_an_empty_secret() {
    let (_tmp, log, _sock) = paths();
    let err = Broker::open_guarded(&log, Vec::new())
        .err()
        .expect("a guarded broker opened with an empty secret");
    assert_eq!(err.kind(), std::io::ErrorKind::InvalidInput, "{err}");
}

/// Over `serve_tcp_identity`, an identity-shaped capability principal (`n-<16 hex>`)
/// must match `identity_principal(&peer_pubkey)` on `Attach`, and `revoke_identity`
/// immediately terminates open connections (without firing their will) and refuses
/// new ones (`REQUIREMENTS` R6).
#[cfg(feature = "identity")]
#[test]
fn identity_principal_binding_and_live_revocation() {
    use astream_broker::{identity_principal, IdentityKeypair};

    let (_tmp, log, _sock) = paths();
    let broker = Broker::open_guarded(&log, SECRET.to_vec()).unwrap();
    let host_key = IdentityKeypair::generate();
    let node_a = IdentityKeypair::generate();
    let node_b = IdentityKeypair::generate();
    let mut h = broker
        .serve_tcp_identity(
            "127.0.0.1:0",
            host_key.clone(),
            vec![node_a.public(), node_b.public()],
        )
        .unwrap();
    let addr = h.tcp_addr().unwrap().to_string();

    let prin_a = identity_principal(&node_a.public());
    let prin_b = identity_principal(&node_b.public());
    let cap_a = mint(SECRET, &format!("rw,p={prin_a}:/a/>")).unwrap();
    let cap_b = mint(SECRET, &format!("rw,p={prin_b}:/a/>")).unwrap();

    // Node A cannot attach Node B's identity-bound capability!
    let mut client_a =
        Client::connect_tcp_identity(&addr, node_a.clone(), host_key.public()).unwrap();
    let err = client_a
        .attach(&cap_b.filter, &cap_b.tag)
        .expect_err("node A must not attach node B's identity-bound grant");
    assert!(
        err.to_string()
            .contains("does not match authenticated peer identity"),
        "{err}"
    );

    // Node A can attach its own identity-bound capability and register a will.
    client_a.attach(&cap_a.filter, &cap_a.tag).unwrap();
    let pid_a = astream_cap::producer_id_of(&prin_a);
    client_a.will(pid_a, 1, "/a/gone", b"revoked-will").unwrap();

    // Live revocation: revoking node A terminates its open connection on the next
    // request, suppresses its will, and refuses any new handshake from node A.
    assert!(broker.revoke_identity(node_a.public()));
    assert!(broker.is_identity_revoked(&node_a.public()));
    let pub_err = client_a
        .publish(pid_a, 2, "/a/x", b"after-revoke")
        .expect_err("revoked peer must be refused on next request");
    assert!(pub_err.to_string().contains("revoked"), "{pub_err}");
    drop(client_a);

    // A new connection from the revoked peer is rejected by the server as soon as
    // M4 identifies the client key (before any request is read).
    let reconnect = Client::connect_tcp_identity(&addr, node_a, host_key.public())
        .and_then(|mut c| c.attach(&cap_a.filter, &cap_a.tag));
    assert!(
        reconnect.is_err(),
        "revoked peer must be refused on reconnect"
    );

    // Node B (unrevoked) verifies that node A's will did NOT fire.
    let mut client_b = Client::connect_tcp_identity(&addr, node_b, host_key.public()).unwrap();
    client_b.attach(&cap_b.filter, &cap_b.tag).unwrap();
    let (recs, _) = client_b.fetch(0, "/a/gone", 16).unwrap();
    assert!(
        recs.is_empty(),
        "revoked peer's will must not fire: {recs:?}"
    );

    h.shutdown();
}

/// Offline bearer-attenuated Macaroon capabilities (`attenuate_offline`, `via=<hex>`)
/// attach against a guarded broker without the bearer possessing the broker's master
/// `SECRET`, and enforce the narrowed child grant (`ro:` vs `rw:`, narrowed subtree).
#[test]
fn offline_macaroon_attenuated_capability_attaches_and_enforces_narrowed_scope() {
    let (_tmp, _b, mut h, sock) = fresh();
    let root = mint(SECRET, "rw,p=n-0102030405060708:/a/>").unwrap();
    let pid = astream_cap::producer_id_of("n-0102030405060708");

    // Bearer derives a narrower read-write sub-capability offline without SECRET:
    let sub_rw =
        astream_cap::attenuate_offline(&root, "rw,p=n-0102030405060708:/a/sub/>", now_ms())
            .unwrap();
    // And derives a second-hop read-only sub-capability offline:
    let sub_ro =
        astream_cap::attenuate_offline(&sub_rw, "ro,p=n-0102030405060708:/a/sub/leaf", now_ms())
            .unwrap();

    let mut pub_client = Client::connect(&sock).unwrap();
    pub_client.attach(&sub_rw.filter, &sub_rw.tag).unwrap();
    // Allowed within `/a/sub/>`:
    let (off, _) = pub_client
        .publish(pid, 1, "/a/sub/leaf", b"macaroon-ok")
        .unwrap();
    assert_eq!(off, 1);
    // Refused outside `/a/sub/>` even though the root capability covered `/a/>`:
    assert!(
        pub_client
            .publish(pid, 2, "/a/other", b"outside-child")
            .is_err(),
        "offline-attenuated child must not authorize parent's wider subtree"
    );

    // Second-hop read-only Macaroon attaches and reads `/a/sub/leaf`, but cannot publish:
    let mut ro_client = Client::connect(&sock).unwrap();
    ro_client.attach(&sub_ro.filter, &sub_ro.tag).unwrap();
    let (recs, _) = ro_client.fetch(0, "/a/sub/leaf", 16).unwrap();
    assert_eq!(recs.len(), 1);
    assert_eq!(recs[0].2, b"macaroon-ok");
    assert!(
        ro_client
            .publish(pid, 3, "/a/sub/leaf", b"ro-cannot-write")
            .is_err(),
        "read-only offline Macaroon must not authorize publish"
    );

    h.shutdown();
}

/// `Client::retire_subject` sends `/a/retire` over the wire, checks capability write
/// authority on the target subject, refuses cross-producer retirement, removes the
/// retired subject from `Client::last`, and decrements `distinct_subjects` in `Broker::stats`.
#[test]
fn client_retire_subject_enforces_cap_and_reclaims_last_over_wire() {
    let (_tmp, broker, mut h, sock) = fresh();
    let cap_a = mint(SECRET, "rw,p=n-0102030405060708:/f/local/pub/n-1/>").unwrap();
    let cap_b = mint(SECRET, "rw,p=n-1111111111111111:/f/local/pub/>").unwrap();
    let cap_ro = mint(SECRET, "ro:/f/local/pub/>").unwrap();
    let pid_a = astream_cap::producer_id_of("n-0102030405060708");
    let pid_b = astream_cap::producer_id_of("n-1111111111111111");

    let mut client_a = Client::connect(&sock).unwrap();
    client_a.attach(&cap_a.filter, &cap_a.tag).unwrap();
    client_a
        .publish(pid_a, 1, "/f/local/pub/n-1/s1/presence", b"live")
        .unwrap();
    client_a
        .publish(pid_a, 2, "/f/local/pub/n-1/s1/ev", b"started")
        .unwrap();
    assert_eq!(broker.stats().log.distinct_subjects, 2);

    // Producer B has filter permission on `/f/local/pub/>` but does NOT own `n-1`'s subject:
    let mut client_b = Client::connect(&sock).unwrap();
    client_b.attach(&cap_b.filter, &cap_b.tag).unwrap();
    assert!(
        client_b
            .retire_subject(pid_b, "/f/local/pub/n-1/s1/presence")
            .is_err(),
        "another producer must not retire pid_a's subject"
    );
    assert_eq!(broker.stats().log.distinct_subjects, 2);

    // Producer A retires its exited session's two subjects over the wire:
    let (_, already_absent) = client_a
        .retire_subject(pid_a, "/f/local/pub/n-1/s1/presence")
        .unwrap();
    assert!(!already_absent);
    let (_, already_absent_again) = client_a
        .retire_subject(pid_a, "/f/local/pub/n-1/s1/presence")
        .unwrap();
    assert!(already_absent_again, "second retire is an idempotent no-op");
    let (_, already_absent_ev) = client_a
        .retire_subject(pid_a, "/f/local/pub/n-1/s1/ev")
        .unwrap();
    assert!(!already_absent_ev);
    assert_eq!(broker.stats().log.distinct_subjects, 0);

    // `Client::last` confirms the subjects are gone from `Last`:
    let mut reader = Client::connect(&sock).unwrap();
    reader.attach(&cap_ro.filter, &cap_ro.tag).unwrap();
    let (rows, _) = reader.last("/f/local/pub/n-1/>", "", 16).unwrap();
    assert!(rows.is_empty());

    h.shutdown();
}

/// `Client::retire_subject` enforces the narrowed §5.2 contract:
/// 1. Exact `Subject` only (wildcard filters are refused with `ERR_BAD_SUBJECT`).
/// 2. Charged producer only (an updater that did not introduce the `Last` entry is
///    refused with `ERR_RETIRE_REFUSED` / `is_retire_charged()`).
/// 3. Refused while a live or durable will that can still append targets the subject
///    (`ERR_RETIRE_REFUSED` / `is_retire_will()`).
/// 4. Refused on a replica (`ERR_REFUSED`). Retention-cut refusal is checked
///    separately when the `retention` API is available.
#[test]
fn client_retire_narrowed_rules_charged_producer_will_and_replica() {
    let (_tmp, log, sock) = paths();
    let broker = Broker::open_guarded(&log, SECRET.to_vec()).unwrap();
    let mut h = broker.serve(&sock).unwrap();

    let cap_a = mint(SECRET, "rw,p=n-0102030405060708:/f/local/pub/>").unwrap();
    let cap_b = mint(SECRET, "rw,p=n-1111111111111111:/f/local/pub/>").unwrap();
    let pid_a = astream_cap::producer_id_of("n-0102030405060708");
    let pid_b = astream_cap::producer_id_of("n-1111111111111111");

    let mut client_a = Client::connect(&sock).unwrap();
    client_a.attach(&cap_a.filter, &cap_a.tag).unwrap();
    let mut client_b = Client::connect(&sock).unwrap();
    client_b.attach(&cap_b.filter, &cap_b.tag).unwrap();

    // Producer A introduces `/f/local/pub/n-1/s1/ev` (charged to pid_a).
    client_a
        .publish(pid_a, 1, "/f/local/pub/n-1/s1/ev", b"v1")
        .unwrap();
    // Producer B updates the same subject (newest writer is pid_b, but charged is pid_a).
    client_b
        .publish(pid_b, 1, "/f/local/pub/n-1/s1/ev", b"v2")
        .unwrap();
    assert_eq!(client_a.subject_budget(pid_a).unwrap().unwrap().subjects, 1);
    assert_eq!(client_b.subject_budget(pid_b).unwrap().unwrap().subjects, 0);

    // 1. Wildcard filters are refused with ERR_BAD_SUBJECT:
    let err_wild = client_a
        .retire_subject(pid_a, "/f/local/pub/n-1/s1/>")
        .unwrap_err();
    assert_eq!(
        astream_broker::broker_refusal(&err_wild).map(|r| r.code),
        Some(astream_broker::proto::ERR_BAD_SUBJECT)
    );

    // 2. Updater (pid_b) cannot retire a subject charged to pid_a:
    let err_charged = client_b
        .retire_subject(pid_b, "/f/local/pub/n-1/s1/ev")
        .unwrap_err();
    let ref_charged = astream_broker::broker_refusal(&err_charged).unwrap();
    assert!(ref_charged.is_retire_refused() && ref_charged.is_retire_charged());

    // 3. While a will that can still append targets `/f/local/pub/n-1/s1/ev`, retire is refused:
    client_a
        .will(pid_a, 5, "/f/local/pub/n-1/s1/ev", b"bye")
        .unwrap();
    let err_will = client_a
        .retire_subject(pid_a, "/f/local/pub/n-1/s1/ev")
        .unwrap_err();
    let ref_will = astream_broker::broker_refusal(&err_will).unwrap();
    assert!(ref_will.is_retire_refused() && ref_will.is_retire_will());

    // Once pid_a fences its will (seq 6 > 5), pid_a can retire the subject:
    client_a
        .publish(pid_a, 6, "/f/local/pub/n-1/s1/ev", b"fenced")
        .unwrap();
    let (_, already_absent) = client_a
        .retire_subject(pid_a, "/f/local/pub/n-1/s1/ev")
        .unwrap();
    assert!(!already_absent);
    assert_eq!(client_a.subject_budget(pid_a).unwrap().unwrap().subjects, 0);

    h.shutdown();
    drop(broker);

    // 4. On a replica log, retire is refused with ERR_REFUSED:
    let (_tmp_r, log_r, sock_r) = paths();
    let replica = Broker::open_replica(&log_r).unwrap();
    let mut hr = replica.serve(&sock_r).unwrap();
    let mut cr = Client::connect(&sock_r).unwrap();
    let err_rep = cr
        .retire_subject(pid_a, "/f/local/pub/n-1/s2/ev")
        .unwrap_err();
    assert_eq!(
        astream_broker::broker_refusal(&err_rep).map(|r| r.code),
        Some(astream_broker::proto::ERR_REFUSED)
    );
    hr.shutdown();
}

/// An uncarried retention cut (`retain_before`) refuses retirement without changing
/// the retained subject or its producer charge (`is_retire_cut()`), whereas
/// state-carrying compaction (`retain_before_carrying_state`) carries `last_owner`
/// (`carried_charges`) in `<log>.state` so retirement and `max_subjects_per_producer`
/// charging remain exact across compaction and reopen.
#[cfg(feature = "retention")]
#[test]
fn client_retire_narrowed_rules_refuse_a_retention_cut() {
    let (_tmp, log, sock) = paths();
    let broker = Broker::open_guarded(&log, SECRET.to_vec()).unwrap();
    let mut h = broker.serve(&sock).unwrap();
    let cap_a = mint(SECRET, "rw,p=n-0102030405060708:/f/local/pub/>").unwrap();
    let cap_b = mint(SECRET, "rw,p=n-1111111111111111:/f/local/pub/>").unwrap();
    let pid_a = astream_cap::producer_id_of("n-0102030405060708");
    let pid_b = astream_cap::producer_id_of("n-1111111111111111");

    let mut client_a = Client::connect(&sock).unwrap();
    client_a.attach(&cap_a.filter, &cap_a.tag).unwrap();
    let mut client_b = Client::connect(&sock).unwrap();
    client_b.attach(&cap_b.filter, &cap_b.tag).unwrap();

    // 1. State-carrying compaction (`retain_before_carrying_state`) carries `last_owner`
    // (`carried_charges`) in `<log>.state`, even when another producer overwrites the
    // subject above `base`:
    client_a
        .publish(pid_a, 1, "/f/local/pub/n-1/s2/ev", b"keep-a")
        .unwrap();
    client_b
        .publish(pid_b, 1, "/f/local/pub/n-1/s2/ev", b"overwritten-by-b")
        .unwrap();
    assert_eq!(broker.retain_before_carrying_state(1).unwrap(), 1);
    assert_eq!(broker.stats().log.base.0, 1);
    h.shutdown();
    drop(broker);

    let broker_reopened = Broker::open_guarded(&log, SECRET.to_vec()).unwrap();
    let mut h_reopened = broker_reopened.serve(&sock).unwrap();
    let mut ca2 = Client::connect(&sock).unwrap();
    ca2.hello().unwrap();
    ca2.attach(&cap_a.filter, &cap_a.tag).unwrap();
    let mut cb2 = Client::connect(&sock).unwrap();
    cb2.hello().unwrap();
    cb2.attach(&cap_b.filter, &cap_b.tag).unwrap();

    assert_eq!(ca2.subject_budget(pid_a).unwrap().unwrap().subjects, 1);
    assert_eq!(cb2.subject_budget(pid_b).unwrap().unwrap().subjects, 0);
    let err_b_after_carry = cb2
        .retire_subject(pid_b, "/f/local/pub/n-1/s2/ev")
        .unwrap_err();
    assert!(astream_broker::broker_refusal(&err_b_after_carry)
        .unwrap()
        .is_retire_charged());
    let (_, absent_after_carry) = ca2.retire_subject(pid_a, "/f/local/pub/n-1/s2/ev").unwrap();
    assert!(!absent_after_carry);
    assert_eq!(ca2.subject_budget(pid_a).unwrap().unwrap().subjects, 0);
    h_reopened.shutdown();
    drop(broker_reopened);

    // 2. An uncarried retention cut (`retain_before`) taints the log and refuses
    // retirement with `is_retire_cut()` without changing the retained subject or its
    // producer charge:
    let (_tmp_u, log_u, sock_u) = paths();
    let broker_u = Broker::open_guarded(&log_u, SECRET.to_vec()).unwrap();
    let mut hu = broker_u.serve(&sock_u).unwrap();
    let cap_unbound = mint(SECRET, "rw:/f/local/pub/>").unwrap();
    let mut cu = Client::connect(&sock_u).unwrap();
    cu.attach(&cap_unbound.filter, &cap_unbound.tag).unwrap();
    cu.publish(pid_a, 1, "/f/local/pub/n-1/ev", b"old").unwrap();
    cu.publish(pid_a, 2, "/f/local/pub/n-1/ev", b"kept")
        .unwrap();
    assert_eq!(broker_u.retain_before(1).unwrap(), 1);
    assert_eq!(broker_u.stats().log.base.0, 1);

    let before = cu.last("/f/local/pub/n-1/>", "", 16).unwrap();
    assert_eq!(before.0.len(), 1);
    assert_eq!(cu.subject_budget(pid_a).unwrap().unwrap().subjects, 1);
    let error = cu.retire_subject(pid_a, "/f/local/pub/n-1/ev").unwrap_err();
    assert!(astream_broker::broker_refusal(&error)
        .unwrap()
        .is_retire_cut());
    assert_eq!(cu.last("/f/local/pub/n-1/>", "", 16).unwrap(), before);
    assert_eq!(cu.subject_budget(pid_a).unwrap().unwrap().subjects, 1);
    hu.shutdown();
}

/// Conditional `Client::retire(producer_id, subject, offset, log)` (§5.2):
/// - `Hello` announces `REQUEST_RETIRE` in `NonceExt` tag `0x03` (`supports_retire() == true`).
/// - Refuses mismatched `log`, `offset >= head` when absent, and `offset > cur_off` when present
///   with `ERR_RETIRE_REFUSED` (`is_retire_log()`).
/// - When `offset == cur_off`, enforces charged-producer and live/durable will checks, appends a
///   marked `/a/retire` record `(r_off, false)`, removes `subject` from `Last`, and credits budget.
/// - Retry of `(subject, cur_off, log)` after retirement returns `(visible_head, true)` (moot)
///   without appending another record.
/// - When `subject` was superseded at `o2 > o1`, `retire(..., o1, log)` returns `(o2, true)` (moot)
///   without retiring the newer record at `o2` or crediting the subject's budget.
#[test]
fn client_conditional_retire_verb_cas_moot_supersede_and_nonce_ext() {
    let (_tmp, log, sock) = paths();
    let broker = Broker::open_guarded(&log, SECRET.to_vec()).unwrap();
    let mut h = broker.serve(&sock).unwrap();

    let cap_a = mint(SECRET, "rw,p=n-0102030405060708:/f/local/pub/>").unwrap();
    let cap_b = mint(SECRET, "rw,p=n-1111111111111111:/f/local/pub/>").unwrap();
    let pid_a = astream_cap::producer_id_of("n-0102030405060708");
    let pid_b = astream_cap::producer_id_of("n-1111111111111111");

    let mut client_a = Client::connect(&sock).unwrap();
    assert!(!client_a.supports_retire());
    client_a.hello().unwrap();
    assert!(client_a.supports_retire());
    let log_id = client_a.log_identity().unwrap().unwrap();
    assert_eq!(log_id, broker.log_identity());
    client_a.attach(&cap_a.filter, &cap_a.tag).unwrap();

    let mut client_b = Client::connect(&sock).unwrap();
    client_b.hello().unwrap();
    client_b.attach(&cap_b.filter, &cap_b.tag).unwrap();

    let subj = "/f/local/pub/n-1/s1/ev";
    let head0 = broker.head();

    // Absent subject with offset >= head is refused with is_retire_log():
    let err_ahead_empty = client_a.retire(pid_a, subj, head0, log_id).unwrap_err();
    let ref_ahead_empty = astream_broker::broker_refusal(&err_ahead_empty).unwrap();
    assert!(ref_ahead_empty.is_retire_refused() && ref_ahead_empty.is_retire_log());

    // Publish initial record at offset `head0` (charged to pid_a):
    let (o1, _) = client_a.publish(pid_a, 1, subj, b"v1").unwrap();
    assert_eq!(o1, head0);

    // Wrong log identity is refused with is_retire_log():
    let wrong_log = astream_broker::LogIdentity {
        id: log_id.id,
        generation: log_id.generation.wrapping_add(1),
    };
    let err_wrong_log = client_a.retire(pid_a, subj, o1, wrong_log).unwrap_err();
    let ref_wrong_log = astream_broker::broker_refusal(&err_wrong_log).unwrap();
    assert!(ref_wrong_log.is_retire_refused() && ref_wrong_log.is_retire_log());

    // Present at o1, but caller claims offset o1 + 5 > o1: refused with is_retire_log():
    let err_future_off = client_a.retire(pid_a, subj, o1 + 5, log_id).unwrap_err();
    let ref_future_off = astream_broker::broker_refusal(&err_future_off).unwrap();
    assert!(ref_future_off.is_retire_refused() && ref_future_off.is_retire_log());

    // Exact match (offset == o1), but wrong producer (pid_b): refused with is_retire_charged():
    let err_charged = client_b.retire(pid_b, subj, o1, log_id).unwrap_err();
    let ref_charged = astream_broker::broker_refusal(&err_charged).unwrap();
    assert!(ref_charged.is_retire_refused() && ref_charged.is_retire_charged());

    // Exact match (offset == o1) by charged producer (pid_a) succeeds and appends at offset o1 + 1:
    let (r_off, already_absent) = client_a.retire(pid_a, subj, o1, log_id).unwrap();
    assert_eq!((r_off, already_absent), (o1 + 1, false));
    assert_eq!(broker.head(), o1 + 2);
    assert_eq!(client_a.subject_budget(pid_a).unwrap().unwrap().subjects, 0);

    // Retrying the exact same conditional retire `(subj, o1, log_id)` is now MOOT:
    // returns `(visible_head, true)` and appends NO new record!
    let (moot_head, moot_absent) = client_a.retire(pid_a, subj, o1, log_id).unwrap();
    assert_eq!((moot_head, moot_absent), (o1 + 2, true));
    assert_eq!(
        broker.head(),
        o1 + 2,
        "moot retire must not append a record"
    );

    // Superseding publish test:
    // pid_a re-introduces `subj` at o2, then pid_b updates it at o3.
    let (o2, _) = client_a.publish(pid_a, 2, subj, b"v2").unwrap();
    assert_eq!(o2, o1 + 2);
    let (o3, _) = client_b.publish(pid_b, 1, subj, b"v3").unwrap();
    assert_eq!(o3, o1 + 3);
    assert_eq!(broker.head(), o1 + 4);

    // A stale conditional retire targeting `o2` (< `o3`) is MOOT: returns `(o3, true)`
    // and leaves the newer record at `o3` intact in `Last` and budget charged to `pid_a`!
    let (superseded_off, superseded_moot) = client_a.retire(pid_a, subj, o2, log_id).unwrap();
    assert_eq!((superseded_off, superseded_moot), (o3, true));
    assert_eq!(
        broker.head(),
        o1 + 4,
        "superseded retire must not append a record"
    );
    assert_eq!(client_a.subject_budget(pid_a).unwrap().unwrap().subjects, 1);
    let (rows, _) = client_a.last(subj, "", 8).unwrap();
    assert_eq!(rows.len(), 1);
    assert_eq!((rows[0].0, rows[0].2.as_slice()), (o3, b"v3".as_slice()));

    // Retiring at the current offset `o3` succeeds:
    let (r2_off, r2_absent) = client_a.retire(pid_a, subj, o3, log_id).unwrap();
    assert_eq!((r2_off, r2_absent), (o1 + 4, false));
    assert_eq!(client_a.subject_budget(pid_a).unwrap().unwrap().subjects, 0);
    let (rows_after, _) = client_a.last(subj, "", 8).unwrap();
    assert!(rows_after.is_empty());

    h.shutdown();
}

/// Revocation file automatic `SIGHUP` reload and capability-principal live revocation
/// (`REQUIREMENTS` R6, `ROADMAP.md`):
/// - `load_revocation_file` parses atomically and fail-closed, and installs the `SIGHUP`
///   handler so `kill -HUP <pid>` reloads the file in place.
/// - Adding a capability principal (`s-sub` / `s-will`) to the revocation file and sending
///   `SIGHUP` terminates an already-open subscription authorized by `s-sub` with an
///   `unauthorized` error, refuses new requests under `s-will`, and suppresses `s-will`'s
///   pending last will on disconnect.
/// - A malformed edit on `SIGHUP` fails closed (preserving existing revocations), while
///   removing a file-loaded entry and sending `SIGHUP` unrevokes it without disturbing
///   manual `revoke_principal` entries.
#[cfg(target_vendor = "apple")]
#[test]
fn sighup_reloads_revocation_file_and_revokes_open_principal_subscriptions_and_wills() {
    let (tmp, log, sock) = paths();
    let rev_path = format!("{log}.revocations");
    let _rev_clean = Cleanup::new(&[&rev_path]);
    let _ = &tmp;

    std::fs::write(&rev_path, "# initial revocation file\ns-initial\n").unwrap();

    let broker = Broker::open_guarded(&log, SECRET.to_vec()).unwrap();
    broker.set_liveness_poll(Duration::from_millis(25));
    assert_eq!(broker.load_revocation_file(&rev_path).unwrap(), 1);
    assert!(broker.is_principal_revoked("s-initial"));
    broker.revoke_principal("s-manual");
    assert!(broker.is_principal_revoked("s-manual"));

    let mut h = broker.serve(&sock).unwrap();

    let cap_sub = mint(SECRET, "ro,p=s-sub:/a/>").unwrap();
    let cap_will = mint(SECRET, "rw,p=s-will:/a/>").unwrap();
    let cap_obs = mint(SECRET, "ro,p=s-observer:/a/>").unwrap();
    let pid_will = astream_cap::producer_id_of("s-will");

    // Subscriber opens a live subscription under `s-sub`:
    let mut sub_client = Client::connect(&sock).unwrap();
    sub_client.attach(&cap_sub.filter, &cap_sub.tag).unwrap();

    // Publisher registers a will under `s-will` and publishes an initial record:
    let mut will_client = Client::connect(&sock).unwrap();
    will_client.attach(&cap_will.filter, &cap_will.tag).unwrap();
    will_client
        .will(pid_will, 1, "/a/gone", b"revoked-principal-will")
        .unwrap();
    will_client.publish(pid_will, 2, "/a/x", b"first").unwrap();

    let mut sub = sub_client.subscribe(0, "/a/>").unwrap();
    let (_, _, body) = sub.recv().unwrap().unwrap();
    assert_eq!(body, b"first");

    // Edit the revocation file to revoke `s-sub` and `s-will` (and drop `s-initial`),
    // then send SIGHUP to this process (`kill -HUP <pid>`):
    std::fs::write(&rev_path, "s-sub\ns-will\n").unwrap();
    let pid_str = std::process::id().to_string();
    let status = std::process::Command::new("kill")
        .args(["-HUP", &pid_str])
        .status()
        .unwrap();
    assert!(status.success());

    // The open subscription under `s-sub` wakes on SIGHUP reload and terminates with
    // an `unauthorized` revocation error:
    let sub_err = sub
        .recv()
        .expect_err("open subscription under revoked principal must terminate");
    assert!(
        sub_err.to_string().contains("revoked"),
        "expected revocation error on open subscription, got: {sub_err}"
    );
    assert!(!broker.is_principal_revoked("s-initial"));
    assert!(broker.is_principal_revoked("s-sub"));
    assert!(broker.is_principal_revoked("s-will"));
    assert!(broker.is_principal_revoked("s-manual"));

    // Next publish on `will_client` is refused, and dropping `will_client` suppresses
    // its pending last will:
    assert!(
        will_client
            .publish(pid_will, 3, "/a/x", b"after-revoke")
            .is_err(),
        "revoked principal must not publish"
    );
    drop(will_client);

    let mut obs = Client::connect(&sock).unwrap();
    obs.attach(&cap_obs.filter, &cap_obs.tag).unwrap();
    let (wills, _) = obs.fetch(0, "/a/gone", 16).unwrap();
    assert!(
        wills.is_empty(),
        "revoked principal's will must be suppressed: {wills:?}"
    );

    // A malformed edit to the revocation file followed by SIGHUP fails closed, keeping
    // the existing revocations intact:
    std::fs::write(&rev_path, "not valid entry with spaces!\n").unwrap();
    let status = std::process::Command::new("kill")
        .args(["-HUP", &pid_str])
        .status()
        .unwrap();
    assert!(status.success());
    assert!(broker.is_principal_revoked("s-sub"));
    assert!(broker.is_principal_revoked("s-will"));
    assert!(broker.is_principal_revoked("s-manual"));

    h.shutdown();
}

/// Capability attachment on Replicated-tier follower links (`ROADMAP.md` §Replication):
/// - `Broker::open_replica_guarded` and `Broker::open_replicated_guarded` refuse an
///   empty secret with `InvalidInput`.
/// - A leader whose follower capability is forged (wrong secret) is refused at `Attach`
///   during open and fails fast when `live < quorum`.
/// - A leader whose follower capability is bound (`p=s-bound`) attaches, but is fenced
///   on its first `Replicate` because `Replicate` requires an unbound `rw` grant.
/// - With a valid unbound replication capability (`rw:/>`), the guarded leader attaches
///   the capability (`Hello` -> `Nonce` -> `Attach` -> `Mark`) on every follower link at
///   initial dial and on reconnect after a follower restart, replicating bound publishes
///   (`/a/bind` + data) and group commits across guarded followers at `quorum = 2`.
#[test]
fn replicated_guarded_attaches_follower_capability_and_recovers_across_follower_restart() {
    let (_tmp_l, log_l, sock_l) = paths();
    let (_tmp_f1, log_f1, _sock_f1) = paths();
    let (_tmp_f2, log_f2, _sock_f2) = paths();

    let rep_cap = mint(SECRET, "rw:/>").unwrap();
    assert_eq!(
        Broker::open_replica_guarded(&log_f1, Vec::new())
            .err()
            .unwrap()
            .kind(),
        std::io::ErrorKind::InvalidInput
    );
    assert_eq!(
        Broker::open_replicated_guarded(
            &log_l,
            Vec::new(),
            &["127.0.0.1:1".to_string()],
            rep_cap.clone(),
            1,
        )
        .err()
        .unwrap()
        .kind(),
        std::io::ErrorKind::InvalidInput
    );

    let f1 = Broker::open_replica_guarded(&log_f1, SECRET.to_vec()).unwrap();
    let mut h_f1 = f1.serve_tcp("127.0.0.1:0").unwrap();
    let f1_addr = h_f1.tcp_addr().unwrap().to_string();

    let f2 = Broker::open_replica_guarded(&log_f2, SECRET.to_vec()).unwrap();
    let mut h_f2 = f2.serve_tcp("127.0.0.1:0").unwrap();
    let f2_addr = h_f2.tcp_addr().unwrap().to_string();

    let followers = vec![f1_addr.clone(), f2_addr.clone()];

    // 1. A forged follower capability (minted under the wrong secret) is refused at
    // `Attach` during open, failing fast when `live < quorum`:
    let bad_cap = mint(b"wrong-secret-0123456789abcdef012", "rw:/>").unwrap();
    let err_bad = Broker::open_replicated_guarded(&log_l, SECRET.to_vec(), &followers, bad_cap, 2)
        .err()
        .expect("forged follower capability must fail open_replicated_guarded");
    assert!(
        err_bad.to_string().contains("unauthorized"),
        "expected unauthorized error from follower Attach, got: {err_bad}"
    );

    // 2. Bound (`rw,p=s-bound:/>`) and read-only (`ro:/>`) follower capabilities are
    // refused up front with `InvalidInput` before dialing any follower:
    for invalid_grant in ["rw,p=s-bound:/>", "ro:/>"] {
        let invalid_cap = mint(SECRET, invalid_grant).unwrap();
        assert_eq!(
            Broker::open_replicated_guarded(&log_l, SECRET.to_vec(), &followers, invalid_cap, 2,)
                .err()
                .unwrap()
                .kind(),
            std::io::ErrorKind::InvalidInput
        );
    }

    // 3. Valid unbound replication capability (`rw:/>`) authenticates both follower links,
    // replicates bound publishes (`/a/bind` + data) and group commits at `quorum = 2`,
    // and re-authenticates on reconnect after a follower restart:
    let leader =
        Broker::open_replicated_guarded(&log_l, SECRET.to_vec(), &followers, rep_cap.clone(), 2)
            .unwrap();
    let mut h_l = leader.serve(&sock_l).unwrap();

    let cap_pub = mint(SECRET, "rw,p=s-pub:/a/>").unwrap();
    let cap_sub = mint(SECRET, "ro,p=s-sub:/a/>").unwrap();
    let pid_pub = astream_cap::producer_id_of("s-pub");

    let mut client = Client::connect(&sock_l).unwrap();
    client.attach(&cap_pub.filter, &cap_pub.tag).unwrap();
    let (off1, _) = client.publish(pid_pub, 1, "/a/msg", b"one").unwrap();
    // Offset 0 is `/a/bind`, offset 1 is `/a/msg`:
    assert_eq!(off1, 1);
    client.commit("/a/grp", 2).unwrap();

    // Verify guarded follower f1 holds the replicated records and requires a capability to read:
    let mut c_f1 = Client::connect_tcp(&f1_addr).unwrap();
    assert!(c_f1.fetch(0, "/a/>", 16).is_err());
    c_f1.attach(&cap_sub.filter, &cap_sub.tag).unwrap();
    let (f1_recs, _) = c_f1.fetch(0, "/a/>", 16).unwrap();
    assert_eq!(f1_recs.len(), 1);
    assert_eq!(
        (f1_recs[0].0, f1_recs[0].2.as_slice()),
        (1, b"one".as_slice())
    );

    // Restart follower f2 on the same TCP port (`f2_addr`), then publish a second record
    // requiring `quorum = 2`: the leader's `FollowerLink::reconnect` re-dials `f2_addr`
    // and re-attaches `rep_cap` on the new connection!
    h_f2.shutdown();
    drop(f2);
    let f2_restarted = Broker::open_replica_guarded(&log_f2, SECRET.to_vec()).unwrap();
    let mut h_f2 = f2_restarted.serve_tcp(&f2_addr).unwrap();

    let (off2, _) = client.publish(pid_pub, 2, "/a/msg", b"two").unwrap();
    assert_eq!(off2, 3); // offset 2 was `/a/commit` for `/a/grp`

    let mut c_f2 = Client::connect_tcp(&f2_addr).unwrap();
    c_f2.attach(&cap_sub.filter, &cap_sub.tag).unwrap();
    let (f2_recs, _) = c_f2.fetch(0, "/a/>", 16).unwrap();
    assert_eq!(f2_recs.len(), 2);
    assert_eq!(
        (f2_recs[0].0, f2_recs[0].2.as_slice()),
        (1, b"one".as_slice())
    );
    assert_eq!(
        (f2_recs[1].0, f2_recs[1].2.as_slice()),
        (3, b"two".as_slice())
    );

    h_l.shutdown();
    h_f1.shutdown();
    h_f2.shutdown();
}
