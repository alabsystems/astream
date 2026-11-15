// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Deterministic Seam Effect Byte & Call-Count Budget Gate
//! (`Astream.Effects.TlaSeamEffectBudget`).
//!
//! When an agent session executes or replays recorded `EffectRecord` (`astream_effects::EffectRecord`)
//! side-effects (`Disk`, `Net`, `Clock`, `Process`), an unbounded tool loop can exhaust memory or
//! log capacity before an outer supervisor intervenes.
//!
//! [`SeamEffectBudget`] enforces deterministic byte and call quotas across live execution and
//! deterministic replay:
//! - Cumulative admitted payload bytes stay bounded by `byte_cap` via Clean-origin
//!   [`effect_bytes_clamp`] and contract-verified [`effect_bytes_within_cap`].
//! - Admitted seam effect sequence numbers progress strictly monotonically via Clean-origin
//!   [`effect_seq_advance`], ensuring live runs and replays halt at the exact same effect index.

#[cfg(clean_islands)]
#[path = "effect_budget_island.rs"]
mod effect_budget_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn effect_bytes_clamp(cand_bytes: u64, byte_cap: u64) -> u64 {
    if cand_bytes < byte_cap {
        cand_bytes
    } else {
        byte_cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn effect_seq_advance(cur_seq: u64, cand_seq: u64) -> u64 {
    if cur_seq < cand_seq {
        cand_seq
    } else {
        cur_seq
    }
}
#[cfg(clean_islands)]
pub use effect_budget_island::{effect_bytes_clamp, effect_seq_advance};

/// Default cumulative seam payload byte budget (`32 MiB`).
pub const DEFAULT_SEAM_BYTE_CAP: u64 = 32 * 1024 * 1024;

/// Default maximum seam effect invocations per session (`65_536`).
pub const DEFAULT_SEAM_CALL_CAP: u64 = 65_536;

contract_fn! {
    /// Kernel-certified check that `used_bytes <= byte_cap`, linked via
    /// `clean-kernel-defeq` to `effect_bytes_within_cap_isl`.
    #[must_use]
    pub const fn effect_bytes_within_cap(used_bytes: u64, byte_cap: u64) -> bool
    clauses [ensures result == (used_bytes <= byte_cap)]
    {
        used_bytes <= byte_cap
    }
}

/// Coarse side-effect category accounted against a [`SeamEffectBudget`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EffectBudgetClass {
    ClockOrRng,
    FilesystemIo,
    NetworkIo,
    SubprocessExec,
}

/// Refusal reason when a candidate seam effect exceeds budget or breaks sequence monotonicity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SeamBudgetDenial {
    NonMonotoneSeq { candidate: u64, last_seq: u64 },
    CallCapExceeded { calls_used: u64, call_cap: u64 },
    SinglePayloadTooLarge { payload_bytes: u64, max_single: u64 },
    ByteCapExceeded { projected_bytes: u64, byte_cap: u64 },
}

/// Stateful deterministic seam quota tracker backed by `Astream.Effects.TlaSeamEffectBudget`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SeamEffectBudget {
    used_bytes: u64,
    byte_cap: u64,
    max_single_payload: u64,
    calls_used: u64,
    call_cap: u64,
    last_seq: u64,
    has_any: bool,
}

impl SeamEffectBudget {
    /// Construct a seam budget with `byte_cap`, `max_single_payload`, and `call_cap`.
    #[must_use]
    pub const fn new(byte_cap: u64, max_single_payload: u64, call_cap: u64) -> Self {
        let single = if max_single_payload > byte_cap {
            byte_cap
        } else {
            max_single_payload
        };
        Self {
            used_bytes: 0,
            byte_cap,
            max_single_payload: single,
            calls_used: 0,
            call_cap,
            last_seq: 0,
            has_any: false,
        }
    }

    /// Construct a seam budget with [`DEFAULT_SEAM_BYTE_CAP`] (`32 MiB`), `4 MiB` max single
    /// effect payload, and [`DEFAULT_SEAM_CALL_CAP`].
    #[must_use]
    pub const fn with_defaults() -> Self {
        Self::new(
            DEFAULT_SEAM_BYTE_CAP,
            4 * 1024 * 1024,
            DEFAULT_SEAM_CALL_CAP,
        )
    }

    /// Accounted payload bytes (`<= byte_cap`).
    #[must_use]
    pub const fn used_bytes(&self) -> u64 {
        self.used_bytes
    }

    /// Remaining byte budget (`byte_cap - used_bytes`).
    #[must_use]
    pub const fn remaining_bytes(&self) -> u64 {
        self.byte_cap.saturating_sub(self.used_bytes)
    }

    /// Admitted seam invocation count (`<= call_cap`).
    #[must_use]
    pub const fn calls_used(&self) -> u64 {
        self.calls_used
    }

    /// Highest admitted effect sequence number, if at least one effect was admitted.
    #[must_use]
    pub const fn last_admitted_seq(&self) -> Option<u64> {
        if self.has_any {
            Some(self.last_seq)
        } else {
            None
        }
    }

    /// Admit a candidate seam effect (`cand_seq`, `class`, `payload_bytes`) or fail closed
    /// without mutating accounted counters.
    pub fn admit_effect(
        &mut self,
        cand_seq: u64,
        _class: EffectBudgetClass,
        payload_bytes: u64,
    ) -> Result<u64, SeamBudgetDenial> {
        if self.has_any && cand_seq <= self.last_seq {
            return Err(SeamBudgetDenial::NonMonotoneSeq {
                candidate: cand_seq,
                last_seq: self.last_seq,
            });
        }
        let next_calls = match self.calls_used.checked_add(1) {
            Some(c) if c <= self.call_cap => c,
            _ => {
                return Err(SeamBudgetDenial::CallCapExceeded {
                    calls_used: self.calls_used,
                    call_cap: self.call_cap,
                });
            }
        };
        if payload_bytes > self.max_single_payload {
            return Err(SeamBudgetDenial::SinglePayloadTooLarge {
                payload_bytes,
                max_single: self.max_single_payload,
            });
        }
        let Some(projected) = self.used_bytes.checked_add(payload_bytes) else {
            return Err(SeamBudgetDenial::ByteCapExceeded {
                projected_bytes: u64::MAX,
                byte_cap: self.byte_cap,
            });
        };
        if !effect_bytes_within_cap(projected, self.byte_cap) {
            return Err(SeamBudgetDenial::ByteCapExceeded {
                projected_bytes: projected,
                byte_cap: self.byte_cap,
            });
        }

        self.used_bytes = effect_bytes_clamp(projected, self.byte_cap);
        self.calls_used = next_calls;
        self.last_seq = if self.has_any {
            effect_seq_advance(self.last_seq, cand_seq)
        } else {
            cand_seq
        };
        self.has_any = true;
        Ok(self.used_bytes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_monotone_seq_single_limit_call_cap_and_cumulative_byte_cap() {
        let mut b = SeamEffectBudget::new(1000, 600, 3);
        assert_eq!(
            b.admit_effect(0, EffectBudgetClass::NetworkIo, 400),
            Ok(400)
        );
        assert_eq!(
            b.admit_effect(0, EffectBudgetClass::ClockOrRng, 8),
            Err(SeamBudgetDenial::NonMonotoneSeq {
                candidate: 0,
                last_seq: 0,
            })
        );
        assert_eq!(
            b.admit_effect(1, EffectBudgetClass::FilesystemIo, 700),
            Err(SeamBudgetDenial::SinglePayloadTooLarge {
                payload_bytes: 700,
                max_single: 600,
            })
        );
        assert_eq!(
            b.admit_effect(1, EffectBudgetClass::FilesystemIo, 500),
            Ok(900)
        );
        assert_eq!(
            b.admit_effect(2, EffectBudgetClass::NetworkIo, 200),
            Err(SeamBudgetDenial::ByteCapExceeded {
                projected_bytes: 1100,
                byte_cap: 1000,
            })
        );
        assert_eq!(
            b.admit_effect(2, EffectBudgetClass::ClockOrRng, 100),
            Ok(1000)
        );
        assert_eq!(
            b.admit_effect(3, EffectBudgetClass::ClockOrRng, 0),
            Err(SeamBudgetDenial::CallCapExceeded {
                calls_used: 3,
                call_cap: 3,
            })
        );
        assert_eq!(b.remaining_bytes(), 0);
        assert_eq!(b.last_admitted_seq(), Some(2));
    }
}
