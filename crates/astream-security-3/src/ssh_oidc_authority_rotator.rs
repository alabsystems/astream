// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! External-authority (`SSH agent` / `OIDC`) certificate binder & dual-overlap key rotator
//! (`Astream.Cap.TlaSshOidcAuthorityRotator`).
//!
//! Binds short-lived workload/operator certificates issued by an external authority (SSH CA /
//! ssh-agent or OIDC workload identity issuer) to `astream` capability principals with zero static
//! peer allow-list drift:
//! - Enforces `[not_before_ms, expires_at_ms)` validity windows with a bounded `max_cert_ttl_ms`,
//! - Supports graceful dual-key rotation (`retired_floor_epoch <= active_key_epoch`) so tokens
//!   minted under `active_key_epoch - 1` verify during overlap until `retire_epochs_below` raises
//!   `retired_floor_epoch`.

#[cfg(clean_islands)]
#[path = "ssh_oidc_authority_rotator_island.rs"]
mod ssh_oidc_authority_rotator_island;
#[cfg(clean_islands)]
pub use ssh_oidc_authority_rotator_island::{
    authority_epoch_advance_b126, authority_floor_clamp_b126, authority_ttl_clamp_b126,
};

#[cfg(not(clean_islands))]
/// Monotonically advance the external authority's active signing key epoch.
#[must_use]
pub const fn authority_epoch_advance_b126(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

#[cfg(not(clean_islands))]
/// Clamp the retired key floor epoch to `<= active_key_epoch`.
#[must_use]
pub const fn authority_floor_clamp_b126(cand_floor: u64, active_epoch: u64) -> u64 {
    if cand_floor < active_epoch {
        cand_floor
    } else {
        active_epoch
    }
}

#[cfg(not(clean_islands))]
/// Clamp a short-lived certificate TTL to `max_ttl_ms`.
#[must_use]
pub const fn authority_ttl_clamp_b126(requested_ttl_ms: u64, max_ttl_ms: u64) -> u64 {
    if requested_ttl_ms < max_ttl_ms {
        requested_ttl_ms
    } else {
        max_ttl_ms
    }
}

contract_fn! {
    /// True iff `cert_key_epoch` falls within `[retired_floor_epoch, active_key_epoch]`.
    #[must_use]
    pub const fn authority_cert_epoch_live_b126(
        cert_key_epoch: u64,
        retired_floor_epoch: u64,
        active_key_epoch: u64,
    ) -> bool
    clauses [ensures result == (cert_key_epoch >= retired_floor_epoch && cert_key_epoch <= active_key_epoch)]
    {
        cert_key_epoch >= retired_floor_epoch && cert_key_epoch <= active_key_epoch
    }
}

/// External authority kind attesting a peer's transport key and principal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExternalAuthorityKind {
    SshAgentCaCert,
    OidcWorkloadToken,
}

/// Short-lived identity certificate attested by an SSH CA or OIDC issuer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExternalAuthorityCert {
    pub kind: ExternalAuthorityKind,
    pub issuer_fingerprint: u64,
    pub principal_fingerprint: u64,
    pub key_epoch: u64,
    pub not_before_ms: u64,
    pub expires_at_ms: u64,
}

/// Verification verdict for an external-authority certificate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AuthorityCertVerdict {
    Verified {
        principal_fingerprint: u64,
        key_epoch: u64,
        clamped_remaining_ttl_ms: u64,
    },
    RefusedUntrustedIssuer {
        issuer_fingerprint: u64,
    },
    RefusedRetiredOrFutureEpoch {
        cert_epoch: u64,
        retired_floor_epoch: u64,
        active_key_epoch: u64,
    },
    RefusedNotYetValid {
        now_ms: u64,
        not_before_ms: u64,
    },
    RefusedExpired {
        now_ms: u64,
        expires_at_ms: u64,
    },
    RefusedExcessiveCertLifetime {
        cert_ttl_ms: u64,
        max_cert_ttl_ms: u64,
    },
}

/// Stateful SSH-CA / OIDC authority verifier & dual-overlap key rotator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SshOidcAuthorityRotator {
    trusted_issuer_fp: u64,
    retired_floor_epoch: u64,
    active_key_epoch: u64,
    max_cert_ttl_ms: u64,
}

impl SshOidcAuthorityRotator {
    #[must_use]
    pub const fn new(trusted_issuer_fp: u64, initial_epoch: u64, max_cert_ttl_ms: u64) -> Self {
        Self {
            trusted_issuer_fp,
            retired_floor_epoch: initial_epoch,
            active_key_epoch: initial_epoch,
            max_cert_ttl_ms,
        }
    }

    /// Stage a new authority signing key epoch while keeping `retired_floor_epoch` open for overlap.
    pub fn rotate_to_epoch(&mut self, next_epoch: u64) -> u64 {
        self.active_key_epoch = authority_epoch_advance_b126(self.active_key_epoch, next_epoch);
        self.active_key_epoch
    }

    /// Retire old authority signing key epochs strictly below `min(new_floor, active_key_epoch)`.
    pub fn retire_epochs_below(&mut self, new_floor: u64) -> u64 {
        let raised = authority_epoch_advance_b126(self.retired_floor_epoch, new_floor);
        self.retired_floor_epoch = authority_floor_clamp_b126(raised, self.active_key_epoch);
        self.retired_floor_epoch
    }

    /// Verify an SSH-agent CA certificate or OIDC workload token at `now_ms`.
    #[must_use]
    pub const fn verify_cert(
        &self,
        cert: &ExternalAuthorityCert,
        now_ms: u64,
    ) -> AuthorityCertVerdict {
        if cert.issuer_fingerprint != self.trusted_issuer_fp {
            return AuthorityCertVerdict::RefusedUntrustedIssuer {
                issuer_fingerprint: cert.issuer_fingerprint,
            };
        }
        if !authority_cert_epoch_live_b126(
            cert.key_epoch,
            self.retired_floor_epoch,
            self.active_key_epoch,
        ) {
            return AuthorityCertVerdict::RefusedRetiredOrFutureEpoch {
                cert_epoch: cert.key_epoch,
                retired_floor_epoch: self.retired_floor_epoch,
                active_key_epoch: self.active_key_epoch,
            };
        }
        if now_ms < cert.not_before_ms {
            return AuthorityCertVerdict::RefusedNotYetValid {
                now_ms,
                not_before_ms: cert.not_before_ms,
            };
        }
        if now_ms >= cert.expires_at_ms {
            return AuthorityCertVerdict::RefusedExpired {
                now_ms,
                expires_at_ms: cert.expires_at_ms,
            };
        }
        let cert_ttl = cert.expires_at_ms.saturating_sub(cert.not_before_ms);
        if cert_ttl > self.max_cert_ttl_ms {
            return AuthorityCertVerdict::RefusedExcessiveCertLifetime {
                cert_ttl_ms: cert_ttl,
                max_cert_ttl_ms: self.max_cert_ttl_ms,
            };
        }
        let rem = cert.expires_at_ms.saturating_sub(now_ms);
        AuthorityCertVerdict::Verified {
            principal_fingerprint: cert.principal_fingerprint,
            key_epoch: cert.key_epoch,
            clamped_remaining_ttl_ms: authority_ttl_clamp_b126(rem, self.max_cert_ttl_ms),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn supports_overlap_key_rotation_and_enforces_short_lived_ssh_oidc_ttl_bounds() {
        let mut rot = SshOidcAuthorityRotator::new(0xCA_F00D, 5, 60_000);
        // Rotate to epoch 6 while keeping epoch 5 live during grace overlap.
        assert_eq!(rot.rotate_to_epoch(6), 6);

        let cert_v5 = ExternalAuthorityCert {
            kind: ExternalAuthorityKind::SshAgentCaCert,
            issuer_fingerprint: 0xCA_F00D,
            principal_fingerprint: 0xABCD_1234,
            key_epoch: 5,
            not_before_ms: 1_000,
            expires_at_ms: 31_000,
        };
        assert_eq!(
            rot.verify_cert(&cert_v5, 11_000),
            AuthorityCertVerdict::Verified {
                principal_fingerprint: 0xABCD_1234,
                key_epoch: 5,
                clamped_remaining_ttl_ms: 20_000,
            }
        );

        // Retire epoch 5 -> cert_v5 now fails closed while epoch 6 stays active!
        assert_eq!(rot.retire_epochs_below(6), 6);
        assert_eq!(
            rot.verify_cert(&cert_v5, 11_000),
            AuthorityCertVerdict::RefusedRetiredOrFutureEpoch {
                cert_epoch: 5,
                retired_floor_epoch: 6,
                active_key_epoch: 6,
            }
        );

        // Over-long OIDC cert (> 60_000 ms) is refused even under active epoch 6.
        let overlong_oidc = ExternalAuthorityCert {
            kind: ExternalAuthorityKind::OidcWorkloadToken,
            issuer_fingerprint: 0xCA_F00D,
            principal_fingerprint: 0xABCD_1234,
            key_epoch: 6,
            not_before_ms: 1_000,
            expires_at_ms: 90_000,
        };
        assert_eq!(
            rot.verify_cert(&overlong_oidc, 10_000),
            AuthorityCertVerdict::RefusedExcessiveCertLifetime {
                cert_ttl_ms: 89_000,
                max_cert_ttl_ms: 60_000,
            }
        );
    }
}
