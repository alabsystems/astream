// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Strict-only pre-bind & fail-closed `<log>.hw` anti-rollback watermark state machine
//! (`Astream.Broker.TlaPrebindWatermarkGuard`, Island #295).
//!
//! Enforces `broker.log-anti-rollback`'s core invariants:
//! 1. Verified anti-rollback opens are strictly `Strict`-tier only (weaker tiers ack heads that
//!    power loss can take back below a persisted watermark).
//! 2. Before the very first record lands on an empty log, `prebind_first_tag` binds `<log>.hw`
//!    at `watermark = 0` to `first_frame_tag`, so a crash before record 0 lands reopens cleanly.
//! 3. Any failed watermark write latches `poisoned = true` fail-closed until reopen.

#[cfg(clean_islands)]
#[path = "prebind_watermark_guard_island.rs"]
mod prebind_watermark_guard_island;
#[cfg(clean_islands)]
pub use prebind_watermark_guard_island::{anti_rollback_base_clamp, anti_rollback_hw_advance};
#[cfg(not(clean_islands))]
#[must_use]
pub const fn anti_rollback_hw_advance(prev_hw: u64, next_head: u64) -> u64 {
    if prev_hw < next_head {
        next_head
    } else {
        prev_hw
    }
}
#[cfg(not(clean_islands))]
#[must_use]
pub const fn anti_rollback_base_clamp(base: u64, hw: u64) -> u64 {
    if base < hw {
        base
    } else {
        hw
    }
}

contract_fn! {
    /// Verified check that a recovered log head meets or exceeds the persisted anti-rollback
    /// watermark (`watermark <= recovered_head`), linked via `clean-kernel-defeq` to
    /// `anti_rollback_head_valid_isl`.
    #[must_use]
    pub const fn anti_rollback_head_valid(watermark: u64, recovered_head: u64) -> bool
    clauses [ensures result == (watermark <= recovered_head)]
    {
        watermark <= recovered_head
    }
}

/// Errors returned by [`PrebindWatermarkGuard`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AntiRollbackError {
    /// Verified anti-rollback open requested at a non-Strict durability tier.
    RequiresStrictDurability,
    /// Non-empty log is missing `<log>.hw`.
    MissingWatermarkOnNonEmptyLog,
    /// `<log>.hw` tag does not match the log's first frame identity tag.
    ForeignLogWatermarkTag,
    /// `<log>.base` does not match the base authenticated inside `<log>.hw`.
    TamperedBaseSidecar { expected_base: u64, found_base: u64 },
    /// Recovered head fell below persisted `watermark` (tail truncation / rollback!).
    RollbackDetected { watermark: u64, recovered_head: u64 },
    /// Prior watermark write failed; log is poisoned fail-closed until reopen.
    LogPoisonedByFailedWatermarkWrite,
}

/// Stateful `<log>.hw` pre-bind & monotone watermark guard.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PrebindWatermarkGuard {
    bound_tag: Option<[u8; 16]>,
    base: u64,
    watermark: u64,
    poisoned: bool,
}

impl PrebindWatermarkGuard {
    /// Verify and open an anti-rollback state against recovered disk metadata.
    pub fn open_verified(
        is_strict_tier: bool,
        recovered_base: u64,
        recovered_head: u64,
        first_frame_tag: Option<[u8; 16]>,
        persisted_hw: Option<([u8; 16], u64, u64)>,
    ) -> Result<Self, AntiRollbackError> {
        if !is_strict_tier {
            return Err(AntiRollbackError::RequiresStrictDurability);
        }
        match (first_frame_tag, persisted_hw) {
            (None, None) => {
                if recovered_head > 0 {
                    return Err(AntiRollbackError::MissingWatermarkOnNonEmptyLog);
                }
                Ok(Self {
                    bound_tag: None,
                    base: 0,
                    watermark: 0,
                    poisoned: false,
                })
            }
            (None, Some((hw_tag, hw_base, hw_head))) => {
                // Pre-bound before first record landed and crashed before record 0 persisted:
                if !anti_rollback_head_valid(hw_head, recovered_head) {
                    return Err(AntiRollbackError::RollbackDetected {
                        watermark: hw_head,
                        recovered_head,
                    });
                }
                if hw_base != recovered_base {
                    return Err(AntiRollbackError::TamperedBaseSidecar {
                        expected_base: hw_base,
                        found_base: recovered_base,
                    });
                }
                Ok(Self {
                    bound_tag: Some(hw_tag),
                    base: anti_rollback_base_clamp(hw_base, hw_head),
                    watermark: hw_head,
                    poisoned: false,
                })
            }
            (Some(_), None) => Err(AntiRollbackError::MissingWatermarkOnNonEmptyLog),
            (Some(log_tag), Some((hw_tag, hw_base, hw_head))) => {
                if log_tag != hw_tag {
                    return Err(AntiRollbackError::ForeignLogWatermarkTag);
                }
                if hw_base != recovered_base {
                    return Err(AntiRollbackError::TamperedBaseSidecar {
                        expected_base: hw_base,
                        found_base: recovered_base,
                    });
                }
                if !anti_rollback_head_valid(hw_head, recovered_head) {
                    return Err(AntiRollbackError::RollbackDetected {
                        watermark: hw_head,
                        recovered_head,
                    });
                }
                let next_hw = anti_rollback_hw_advance(hw_head, recovered_head);
                Ok(Self {
                    bound_tag: Some(log_tag),
                    base: anti_rollback_base_clamp(recovered_base, next_hw),
                    watermark: next_hw,
                    poisoned: false,
                })
            }
        }
    }

    /// Current authenticated watermark.
    #[must_use]
    pub const fn watermark(&self) -> u64 {
        self.watermark
    }

    #[must_use]
    pub const fn bound_tag(&self) -> Option<[u8; 16]> {
        self.bound_tag
    }

    #[must_use]
    pub const fn base(&self) -> u64 {
        self.base
    }

    /// True if poisoned by a failed watermark write.
    #[must_use]
    pub const fn is_poisoned(&self) -> bool {
        self.poisoned
    }

    /// Record a commit's watermark write outcome (`hw_write_ok`).
    pub fn record_commit_watermark(
        &mut self,
        first_tag: [u8; 16],
        next_head: u64,
        hw_write_ok: bool,
    ) -> Result<u64, AntiRollbackError> {
        if self.poisoned {
            return Err(AntiRollbackError::LogPoisonedByFailedWatermarkWrite);
        }
        if !hw_write_ok {
            self.poisoned = true;
            return Err(AntiRollbackError::LogPoisonedByFailedWatermarkWrite);
        }
        if self.bound_tag.is_none() {
            self.bound_tag = Some(first_tag);
        }
        self.watermark = anti_rollback_hw_advance(self.watermark, next_head);
        self.base = anti_rollback_base_clamp(self.base, self.watermark);
        Ok(self.watermark)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_strict_only_detects_rollback_and_poisons_on_write_failure() {
        assert_eq!(
            PrebindWatermarkGuard::open_verified(false, 0, 0, None, None),
            Err(AntiRollbackError::RequiresStrictDurability)
        );
        // Pre-bind crash at head=0 reopens cleanly:
        let g0 = PrebindWatermarkGuard::open_verified(true, 0, 0, None, Some(([7u8; 16], 0, 0)))
            .expect("prebind at 0");
        assert_eq!(g0.watermark(), 0);

        // Truncated log below watermark is refused:
        assert_eq!(
            PrebindWatermarkGuard::open_verified(
                true,
                0,
                4,
                Some([7u8; 16]),
                Some(([7u8; 16], 0, 5))
            ),
            Err(AntiRollbackError::RollbackDetected {
                watermark: 5,
                recovered_head: 4,
            })
        );

        // Failed watermark write poisons until reopen:
        let mut g = PrebindWatermarkGuard::open_verified(true, 0, 0, None, None).unwrap();
        assert_eq!(g.record_commit_watermark([9u8; 16], 3, true), Ok(3));
        assert_eq!(
            g.record_commit_watermark([9u8; 16], 6, false),
            Err(AntiRollbackError::LogPoisonedByFailedWatermarkWrite)
        );
        assert!(g.is_poisoned());
        assert_eq!(
            g.record_commit_watermark([9u8; 16], 7, true),
            Err(AntiRollbackError::LogPoisonedByFailedWatermarkWrite)
        );
    }
}
