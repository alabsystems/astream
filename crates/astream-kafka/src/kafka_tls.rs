// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Encrypted and mutually-authenticated wire listener policy and session upgrade state machine
//! for [`crate::server::KafkaServer`] and [`crate::server::KafkaClient`]
//! (Kafka SASL/TLS listeners).
//!
//! Composes wire encryption levels (`Plain`, `Sealed` PSK, forward-secret X25519 `Handshake`,
//! and mutual Ed25519 `Identity` signed-DH) with `astream-kafka`'s SASL authentication
//! (`PLAIN` and `SCRAM-SHA-256`). [`ListenerSecurityPolicy`] evaluates Clean-origin
//! [`kafka_listener_gate_code`] and [`kafka_listener_level_advance`]
//! (`Astream.Kafka.TlaSealedListener`) before admitting data-plane Kafka APIs (`Produce`,
//! `Fetch`, `Metadata`, consumer-group coordination).

#![allow(clippy::large_enum_variant)]

use std::fmt;

#[cfg(clean_islands)]
#[path = "kafka_tls_island.rs"]
mod kafka_tls_island;
#[cfg(not(clean_islands))]
#[must_use]
pub const fn kafka_listener_nonzero_bit(val: u64, one_val: u64) -> u64 {
    if val < 1 {
        0
    } else {
        one_val
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn kafka_listener_req_select(required: u64, present_bit: u64) -> u64 {
    if required < 1 {
        1
    } else {
        present_bit
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn kafka_listener_level_advance(cur_level: u64, proposed_level: u64) -> u64 {
    if cur_level < proposed_level {
        proposed_level
    } else {
        cur_level
    }
}
#[cfg(clean_islands)]
pub use kafka_tls_island::{
    kafka_listener_level_advance, kafka_listener_nonzero_bit, kafka_listener_req_select,
};

/// Four-parameter listener admission gate (`kafka_listener_gate_code_isl`), composed over
/// Clean-origin [`kafka_listener_req_select`] and [`kafka_listener_nonzero_bit`].
#[must_use]
pub const fn kafka_listener_gate_code(
    require_encrypted: u64,
    is_encrypted: u64,
    require_sasl: u64,
    sasl_authed: u64,
) -> u64 {
    let enc_ok = kafka_listener_req_select(
        require_encrypted,
        kafka_listener_nonzero_bit(is_encrypted, 1),
    );
    let sasl_ok =
        kafka_listener_req_select(require_sasl, kafka_listener_nonzero_bit(sasl_authed, 1));
    kafka_listener_nonzero_bit(enc_ok, sasl_ok)
}

contract_fn! {
    /// Verified check that a listener admission gate code equals `1`, linked via
    /// `clean-kernel-defeq` to `kafka_listener_code_allows_isl`.
    #[must_use]
    pub const fn kafka_listener_code_allows(code: u64) -> bool
    clauses [ensures result == (code == 1)]
    {
        code == 1
    }
}

/// Security level code (`0..=4`) ordered monotonically under [`kafka_listener_level_advance`].
pub const LEVEL_PLAINTEXT: u64 = 0;
/// Pre-shared-key XChaCha20-Poly1305 ordered-record stream (`SealedStream`).
pub const LEVEL_SEALED_PSK: u64 = 1;
/// Forward-secret ephemeral X25519 + PSK key agreement (`client_handshake` / `server_handshake` or `AROM` v1 UDP roaming).
pub const LEVEL_HANDSHAKE_FS: u64 = 2;
/// Mutual Ed25519 signed-DH (`client_identity_handshake` / `server_identity_handshake`).
pub const LEVEL_MUTUAL_IDENTITY: u64 = 3;
/// Mutual CA-certified SIGMA (`client_cert_handshake` / `server_cert_handshake`).
pub const LEVEL_CERTIFIED_CA: u64 = 4;
/// Maximum authorized client Ed25519 public keys stored inline on [`KafkaListenerTransport::Identity`].
pub const MAX_AUTHORIZED_CLIENTS: usize = 16;

/// Server-side transport listener mode for [`crate::server::KafkaServer`].
#[derive(Clone, PartialEq, Eq)]
pub enum KafkaListenerTransport {
    /// Unencrypted TCP (`LEVEL_PLAINTEXT`).
    Plain,
    /// Pre-shared-key XChaCha20-Poly1305 encrypted record layer (`LEVEL_SEALED_PSK`).
    Sealed { key: [u8; 32] },
    /// Forward-secret X25519 + PSK key agreement (`LEVEL_HANDSHAKE_FS`).
    Handshake { psk: [u8; 32] },
    /// Mutual Ed25519 signed-DH authenticating clients against `authorized_clients` (`LEVEL_MUTUAL_IDENTITY`).
    Identity {
        host_pub: [u8; 32],
        authorized_clients: [[u8; 32]; MAX_AUTHORIZED_CLIENTS],
        authorized_count: usize,
    },
    /// Mutual CA-certified SIGMA authenticating clients against `ca_count` root CAs (`LEVEL_CERTIFIED_CA`).
    Certified { ca_count: usize },
}

impl fmt::Debug for KafkaListenerTransport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Plain => f.write_str("KafkaListenerTransport::Plain"),
            Self::Sealed { .. } => f.write_str("KafkaListenerTransport::Sealed(<redacted>)"),
            Self::Handshake { .. } => f.write_str("KafkaListenerTransport::Handshake(<redacted>)"),
            Self::Identity {
                authorized_count, ..
            } => write!(
                f,
                "KafkaListenerTransport::Identity(authorized={})",
                authorized_count
            ),
            Self::Certified { ca_count } => {
                write!(f, "KafkaListenerTransport::Certified(cas={})", ca_count)
            }
        }
    }
}

impl KafkaListenerTransport {
    /// Security level (`0..=4`) guaranteed by connections accepted on this listener.
    #[must_use]
    pub const fn security_level(&self) -> u64 {
        match self {
            Self::Plain => LEVEL_PLAINTEXT,
            Self::Sealed { .. } => LEVEL_SEALED_PSK,
            Self::Handshake { .. } => LEVEL_HANDSHAKE_FS,
            Self::Identity { .. } => LEVEL_MUTUAL_IDENTITY,
            Self::Certified { .. } => LEVEL_CERTIFIED_CA,
        }
    }

    /// Whether this listener encrypts and authenticates wire frames (`level > 0`).
    #[must_use]
    pub const fn is_encrypted(&self) -> bool {
        self.security_level() > LEVEL_PLAINTEXT
    }

    /// Verify whether `peer_pub` is listed in `authorized_clients` (up to `authorized_count`).
    #[must_use]
    pub fn admits_peer_identity(&self, peer_pub: &[u8; 32]) -> bool {
        match self {
            Self::Identity {
                authorized_clients,
                authorized_count,
                ..
            } => {
                let limit = if *authorized_count <= MAX_AUTHORIZED_CLIENTS {
                    *authorized_count
                } else {
                    MAX_AUTHORIZED_CLIENTS
                };
                let (active, _) = authorized_clients.split_at(limit);
                let mut rest = active;
                while let &[ref candidate, ref tail @ ..] = rest {
                    if candidate == peer_pub {
                        return true;
                    }
                    rest = tail;
                }
                false
            }
            Self::Plain | Self::Sealed { .. } | Self::Handshake { .. } | Self::Certified { .. } => {
                false
            }
        }
    }
}

/// Client-side transport dial credentials for [`crate::server::KafkaClient`].
#[derive(Clone, PartialEq, Eq)]
pub enum KafkaClientTransport {
    /// Unencrypted TCP (`LEVEL_PLAINTEXT`).
    Plain,
    /// Pre-shared-key XChaCha20-Poly1305 encrypted record layer (`LEVEL_SEALED_PSK`).
    Sealed { key: [u8; 32] },
    /// Forward-secret X25519 + PSK key agreement (`LEVEL_HANDSHAKE_FS`).
    Handshake { psk: [u8; 32] },
    /// Mutual Ed25519 signed-DH pinning `expected_server` (`LEVEL_MUTUAL_IDENTITY`).
    Identity {
        client_pub: [u8; 32],
        expected_server: [u8; 32],
    },
    /// Mutual CA-certified SIGMA (`LEVEL_CERTIFIED_CA`).
    Certified { client_pub: [u8; 32] },
}

impl fmt::Debug for KafkaClientTransport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Plain => f.write_str("KafkaClientTransport::Plain"),
            Self::Sealed { .. } => f.write_str("KafkaClientTransport::Sealed(<redacted>)"),
            Self::Handshake { .. } => f.write_str("KafkaClientTransport::Handshake(<redacted>)"),
            Self::Identity { .. } => f.write_str("KafkaClientTransport::Identity(<pinned>)"),
            Self::Certified { .. } => f.write_str("KafkaClientTransport::Certified(<ca>)"),
        }
    }
}

impl KafkaClientTransport {
    /// Security level (`0..=4`) requested by this client dialer.
    #[must_use]
    pub const fn security_level(&self) -> u64 {
        match self {
            Self::Plain => LEVEL_PLAINTEXT,
            Self::Sealed { .. } => LEVEL_SEALED_PSK,
            Self::Handshake { .. } => LEVEL_HANDSHAKE_FS,
            Self::Identity { .. } => LEVEL_MUTUAL_IDENTITY,
            Self::Certified { .. } => LEVEL_CERTIFIED_CA,
        }
    }
}

/// Monotone per-connection security state machine backed by Clean-origin
/// [`kafka_listener_level_advance`] and [`kafka_listener_gate_code`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct KafkaSessionSecurity {
    level: u64,
    sasl_authed: bool,
    peer_identity: Option<[u8; 32]>,
}

impl Default for KafkaSessionSecurity {
    fn default() -> Self {
        Self::new()
    }
}

impl KafkaSessionSecurity {
    /// Construct an initial plaintext, unauthenticated session state.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            level: LEVEL_PLAINTEXT,
            sasl_authed: false,
            peer_identity: None,
        }
    }

    /// Monotonically upgrade transport security level via [`kafka_listener_level_advance`].
    pub fn upgrade_transport(&mut self, proposed_level: u64, peer_identity: Option<[u8; 32]>) {
        let clamped = if proposed_level > LEVEL_CERTIFIED_CA {
            LEVEL_CERTIFIED_CA
        } else {
            proposed_level
        };
        let next = kafka_listener_level_advance(self.level, clamped);
        if next > self.level {
            self.level = next;
            if peer_identity.is_some() {
                self.peer_identity = peer_identity;
            }
        }
    }

    /// Record completed SASL authentication (`PLAIN` or `SCRAM-SHA-256`).
    pub fn mark_sasl_authenticated(&mut self) {
        self.sasl_authed = true;
    }

    /// Current transport security level (`0..=3`).
    #[must_use]
    pub const fn security_level(&self) -> u64 {
        self.level
    }

    /// Whether SASL authentication has succeeded on this connection.
    #[must_use]
    pub const fn is_sasl_authenticated(&self) -> bool {
        self.sasl_authed
    }

    /// Authenticated Ed25519 peer identity if established at [`LEVEL_MUTUAL_IDENTITY`].
    #[must_use]
    pub const fn peer_identity(&self) -> Option<[u8; 32]> {
        self.peer_identity
    }

    /// Evaluate whether `policy` admits data-plane requests in the current session state.
    #[must_use]
    pub const fn admits_data_plane(&self, policy: &ListenerSecurityPolicy) -> bool {
        policy.allows_data_plane(self.level > LEVEL_PLAINTEXT, self.sasl_authed)
    }
}

/// Listener admission policy composing wire encryption and SASL authentication
/// (`Astream.Kafka.TlaSealedListener`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ListenerSecurityPolicy {
    /// Require an encrypted `SealedStream` (`Sealed`, `Handshake`, or `Identity`) before data APIs.
    pub require_encrypted: bool,
    /// Require completed SASL authentication (`PLAIN` or `SCRAM-SHA-256`) before data APIs.
    pub require_sasl: bool,
}

impl ListenerSecurityPolicy {
    /// Evaluate Clean-origin [`kafka_listener_gate_code`] for `(is_encrypted, sasl_authed)`.
    #[must_use]
    pub const fn allows_data_plane(&self, is_encrypted: bool, sasl_authed: bool) -> bool {
        let req_enc: u64 = if self.require_encrypted { 1 } else { 0 };
        let got_enc: u64 = if is_encrypted { 1 } else { 0 };
        let req_sasl: u64 = if self.require_sasl { 1 } else { 0 };
        let got_sasl: u64 = if sasl_authed { 1 } else { 0 };
        let code = kafka_listener_gate_code(req_enc, got_enc, req_sasl, got_sasl);
        kafka_listener_code_allows(code)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn listener_security_policy_truth_table_and_level_monotonicity() {
        let both = ListenerSecurityPolicy {
            require_encrypted: true,
            require_sasl: true,
        };
        assert!(!both.allows_data_plane(false, false));
        assert!(!both.allows_data_plane(true, false));
        assert!(!both.allows_data_plane(false, true));
        assert!(both.allows_data_plane(true, true));

        let enc_only = ListenerSecurityPolicy {
            require_encrypted: true,
            require_sasl: false,
        };
        assert!(!enc_only.allows_data_plane(false, true));
        assert!(enc_only.allows_data_plane(true, false));

        let mut sess = KafkaSessionSecurity::new();
        assert!(!sess.admits_data_plane(&both));
        sess.upgrade_transport(LEVEL_HANDSHAKE_FS, None);
        assert_eq!(sess.security_level(), LEVEL_HANDSHAKE_FS);
        // Downgrade attempts are ignored monotonically.
        sess.upgrade_transport(LEVEL_SEALED_PSK, None);
        assert_eq!(sess.security_level(), LEVEL_HANDSHAKE_FS);
        assert!(!sess.admits_data_plane(&both));
        sess.mark_sasl_authenticated();
        assert!(sess.admits_data_plane(&both));

        let mut auth = [[0u8; 32]; MAX_AUTHORIZED_CLIENTS];
        auth[0] = [7u8; 32];
        let id_listener = KafkaListenerTransport::Identity {
            host_pub: [1u8; 32],
            authorized_clients: auth,
            authorized_count: 1,
        };
        assert!(id_listener.is_encrypted());
        assert!(id_listener.admits_peer_identity(&[7u8; 32]));
        assert!(!id_listener.admits_peer_identity(&[8u8; 32]));

        sess.upgrade_transport(LEVEL_CERTIFIED_CA, Some([9u8; 32]));
        assert_eq!(sess.security_level(), LEVEL_CERTIFIED_CA);
        assert_eq!(sess.peer_identity(), Some([9u8; 32]));
        sess.upgrade_transport(LEVEL_MUTUAL_IDENTITY, Some([1u8; 32]));
        assert_eq!(sess.security_level(), LEVEL_CERTIFIED_CA);
        assert_eq!(sess.peer_identity(), Some([9u8; 32]));
    }
}
