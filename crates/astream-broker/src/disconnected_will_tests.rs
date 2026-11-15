// Copyright 2026 Andrew Yates

//! Disconnect authorization uses fixed times; writer acknowledgements and an
//! ordered flush establish registration and disposal before records are read.

use super::*;

const SECRET: &[u8] = b"disconnected-will-secret";
const PRINCIPAL: &str = "n-0102030405060708";
const CONN: u64 = 7;
const ADMITTED_AT: u64 = 1000;
const EXPIRES_AT: u64 = 1250;
const SUBJECT: &str = "/a/w/gone";
const BODY: &[u8] = b"disconnected-will";

type DeliveredWill = (u64, u64, String, Vec<u8>);

struct Registered {
    broker: Broker,
    stream: Conn,
    reply: UnixStream,
    capability: astream_cap::Capability,
    producer_id: u64,
    will: Vec<(WillRecord, u64)>,
    had_will: bool,
    // The broker and its writer stop before their owned directory is removed.
    _scratch: crate::test_scratch::Scratch,
}

impl Registered {
    fn new(expiry: Option<u64>) -> Self {
        let scratch = crate::test_scratch::Scratch::new("disconnected-will");
        let broker = Broker::open_guarded(scratch.path().join("log"), SECRET.to_vec()).unwrap();
        let grant = match expiry {
            Some(until) => format!("rw,p={PRINCIPAL},exp={until}:/a/w/>"),
            None => format!("rw,p={PRINCIPAL}:/a/w/>"),
        };
        let capability = astream_cap::mint(SECRET, &grant).unwrap();
        let producer_id = astream_cap::producer_id_of(PRINCIPAL);
        let bound = submit_blocking(
            &broker.shared,
            WriteKind::Bind {
                producer_id,
                principal: PRINCIPAL.to_string(),
            },
        );
        assert!(bound.is_ok(), "the real principal binding: {bound:?}");
        let (stream, reply) = UnixStream::pair().unwrap();
        // A stalled writer/response is a test failure, never evidence of expiry.
        stream
            .set_write_timeout(Some(Duration::from_secs(60)))
            .unwrap();
        reply
            .set_read_timeout(Some(Duration::from_secs(60)))
            .unwrap();
        let mut registered = Self {
            broker,
            stream: Conn::Unix(stream),
            reply,
            capability,
            producer_id,
            will: Vec::new(),
            had_will: false,
            _scratch: scratch,
        };
        registered.register(1, SUBJECT, BODY);
        registered
    }

    fn request(&self, producer_seq: u64, subject: &str, body: &[u8]) -> Request {
        Request::Will {
            producer_id: self.producer_id,
            producer_seq,
            subject: subject.to_string(),
            body: body.to_vec(),
        }
    }

    fn register(&mut self, producer_seq: u64, subject: &str, body: &[u8]) {
        let request = self.request(producer_seq, subject, body);
        let until = cap_authorized_until(
            SECRET,
            std::slice::from_ref(&self.capability),
            &request,
            ADMITTED_AT,
        )
        .expect("the real capability authorizes registration at the fixed admission time");
        let mut pipe = None;
        serve_will(
            &self.broker.shared,
            &mut self.stream,
            CONN,
            &mut pipe,
            &mut self.will,
            &mut self.had_will,
            self.producer_id,
            producer_seq,
            subject.to_string(),
            body.to_vec(),
            until,
        )
        .unwrap();
        let response = read_frame(&mut self.reply).unwrap().unwrap();
        assert!(matches!(
            decode_response(&response),
            Some(Response::Mark { .. })
        ));
        assert!(self.had_will);
        assert_eq!(
            self.will.len(),
            1,
            "registration replaces the connection's old will"
        );
        assert_eq!(self.will[0].1, until);
        assert!(
            self.broker
                .shared
                .log
                .lock()
                .unwrap()
                .read_from(Offset::ZERO)
                .iter()
                .any(|record| {
                    record.subject == "/a/will"
                        && record.producer_id == self.producer_id
                        && record.producer_seq == producer_seq
                }),
            "the writer acknowledged a durable registration record"
        );
    }

    fn complete(&mut self, peer: &PeerAuth, now: u64) -> Vec<DeliveredWill> {
        self.complete_with(peer, || now)
    }

    fn complete_with(&mut self, peer: &PeerAuth, clock: impl FnMut() -> u64) -> Vec<DeliveredWill> {
        finish_disconnected_will(
            &self.broker.shared,
            CONN,
            &mut self.will,
            self.had_will,
            peer,
            clock,
        );
        // The same sender queued disposal before this flush. Its ack is the
        // writer barrier; an empty read before the action ran could not pass.
        self.broker.flush_durable().unwrap();
        self.broker
            .shared
            .log
            .lock()
            .unwrap()
            .read_from(Offset::ZERO)
            .into_iter()
            .filter(|record| record.subject.starts_with("/a/w/"))
            .map(|record| {
                (
                    record.producer_id,
                    record.producer_seq,
                    record.subject.clone(),
                    record.body.clone(),
                )
            })
            .collect()
    }

    fn expected(&self, producer_seq: u64, subject: &str, body: &[u8]) -> Vec<DeliveredWill> {
        vec![(
            self.producer_id,
            producer_seq,
            subject.to_string(),
            body.to_vec(),
        )]
    }
}

#[test]
fn capability_deadline_is_checked_at_disconnect_before_at_and_after_expiry() {
    for now in [1249, 1250, 1251] {
        let mut registered = Registered::new(Some(EXPIRES_AT));
        assert_eq!(registered.will[0].1, EXPIRES_AT);
        assert_eq!(
            cap_authorized_until(
                SECRET,
                std::slice::from_ref(&registered.capability),
                &registered.request(1, SUBJECT, BODY),
                EXPIRES_AT,
            ),
            None,
            "new registration is refused at the exact expiry too"
        );
        let expected = if now < EXPIRES_AT {
            registered.expected(1, SUBJECT, BODY)
        } else {
            Vec::new()
        };
        assert_eq!(
            registered.complete(&PeerAuth::none(), now),
            expected,
            "now {now}"
        );
    }
}

#[test]
fn a_nonexpiring_capability_still_fires_at_the_maximum_captured_time() {
    let mut registered = Registered::new(None);
    assert_eq!(registered.will[0].1, u64::MAX);
    let expected = registered.expected(1, SUBJECT, BODY);
    assert_eq!(registered.complete(&PeerAuth::none(), u64::MAX), expected);
}

#[test]
fn the_peer_certificate_deadline_is_independent_of_a_nonexpiring_capability() {
    for now in [1249, 1250, 1251] {
        let mut registered = Registered::new(None);
        let peer = PeerAuth {
            cert_valid_before_ms: Some(EXPIRES_AT),
            ..PeerAuth::none()
        };
        let expected = if now < EXPIRES_AT {
            registered.expected(1, SUBJECT, BODY)
        } else {
            Vec::new()
        };
        assert_eq!(registered.complete(&peer, now), expected, "now {now}");
    }
}

#[test]
fn revoked_capability_principal_or_transport_peer_suppresses_the_registered_will() {
    for case in [
        "principal",
        "identity",
        "certificate",
        "certificate-principal",
        "unrelated",
    ] {
        let mut registered = Registered::new(Some(EXPIRES_AT));
        let mut peer = PeerAuth::none();
        match case {
            "principal" => {
                assert!(registered.broker.revoke_principal(PRINCIPAL));
            }
            "identity" => {
                peer.pubkey = Some([17; 32]);
                assert!(registered.broker.revoke_identity([17; 32]));
            }
            "certificate" => {
                peer.cert_serial = Some(17);
                assert!(registered.broker.revoke_cert_serial(17));
            }
            "certificate-principal" => {
                peer.cert_principal = Some("Peer-Certificate".to_string());
                peer.cert_principal_lower = Some("peer-certificate".to_string());
                assert!(registered.broker.revoke_principal("peer-certificate"));
            }
            "unrelated" => {
                assert!(registered.broker.revoke_principal("unrelated"));
            }
            _ => unreachable!(),
        }
        let expected = if case == "unrelated" {
            registered.expected(1, SUBJECT, BODY)
        } else {
            Vec::new()
        };
        assert_eq!(registered.complete(&peer, 1249), expected, "{case}");
    }
}

#[test]
fn disconnect_uses_the_last_successfully_registered_replacement() {
    let mut registered = Registered::new(Some(EXPIRES_AT));
    registered.register(2, "/a/w/replaced", b"replacement");
    let expected = registered.expected(2, "/a/w/replaced", b"replacement");
    assert_eq!(registered.complete(&PeerAuth::none(), 1249), expected);
}

#[test]
fn the_certificate_clock_is_read_again_after_the_capability_gate() {
    for certificate_now in [1249, 1250] {
        let mut registered = Registered::new(Some(EXPIRES_AT));
        let peer = PeerAuth {
            cert_valid_before_ms: Some(EXPIRES_AT),
            ..PeerAuth::none()
        };
        let expected = if certificate_now < EXPIRES_AT {
            registered.expected(1, SUBJECT, BODY)
        } else {
            Vec::new()
        };
        let mut times = [1249, certificate_now].into_iter();
        assert_eq!(
            registered.complete_with(&peer, || times.next().expect("two deadline reads")),
            expected,
            "capability time 1249, certificate time {certificate_now}"
        );
        assert_eq!(times.next(), None, "both deadline reads were consumed");
    }
}

#[test]
fn disconnect_clock_reads_follow_the_original_short_circuit_order() {
    for (case, expected_calls, fires) in [
        ("no-will", 0, false),
        ("nonexpiring", 0, true),
        ("finite", 1, true),
        ("expired-capability", 1, false),
        ("revoked-peer", 0, false),
        ("revoked-peer-finite", 1, false),
        ("revoked-principal", 1, false),
        ("certificate-max", 1, true),
    ] {
        let expiry = matches!(
            case,
            "finite" | "expired-capability" | "revoked-peer-finite"
        )
        .then_some(EXPIRES_AT);
        let mut registered = Registered::new(expiry);
        let mut peer = PeerAuth::none();
        match case {
            "no-will" => {
                registered.will.clear();
                peer.cert_valid_before_ms = Some(EXPIRES_AT);
            }
            "expired-capability" => peer.cert_valid_before_ms = Some(EXPIRES_AT),
            "revoked-peer" | "revoked-peer-finite" => {
                peer.pubkey = Some([17; 32]);
                peer.cert_valid_before_ms = Some(EXPIRES_AT);
                assert!(registered.broker.revoke_identity([17; 32]));
            }
            "revoked-principal" => {
                peer.cert_valid_before_ms = Some(EXPIRES_AT);
                assert!(registered.broker.revoke_principal(PRINCIPAL));
            }
            "certificate-max" => peer.cert_valid_before_ms = Some(u64::MAX),
            _ => {}
        }
        let mut calls = 0;
        let records = registered.complete_with(&peer, || {
            calls += 1;
            if case == "expired-capability" {
                EXPIRES_AT
            } else {
                1249
            }
        });
        assert_eq!(calls, expected_calls, "{case}");
        let expected = if fires {
            registered.expected(1, SUBJECT, BODY)
        } else {
            Vec::new()
        };
        assert_eq!(records, expected, "{case}");
    }
}
