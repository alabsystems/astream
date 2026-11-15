// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Crash-safe external side-effect idempotency deduplication ledger (`astream-effects`).
//!
//! Ensures agent tool calls and external side effects (`EffectRecord` in `aterm-agent`)
//! execute at-most-once across `aterm ctl @self restart` handoffs and crash recovery:
//!
//! - Before invoking an external mutation, the runner calls [`EffectIdempotencyLedger::begin_effect`]
//!   with `(step_seq, idempotency_key_digest)`.
//! - If already `Committed(receipt_digest)`, `begin_effect` returns
//!   [`EffectBeginDecision::SkipAlreadyCommitted`] with the cached 32-byte receipt digest.
//! - If `InFlight` from an uncompleted crash boundary, returns
//!   [`EffectBeginDecision::ResumeInFlight`] so the caller inspects external state before
//!   re-issuing.
//! - Zero closures (`0 mandated`), backed by Clean TLA+ island `Astream.Effects.TlaEffectIdempotencyLedger`.

#[cfg(clean_islands)]
#[path = "effects_idempotency_ledger_island.rs"]
mod effects_idempotency_ledger_island;
#[cfg(not(clean_islands))]
#[must_use]
pub const fn ledger_recorded_clamp(proposed_recorded: u64, ledger_cap: u64) -> u64 {
    if proposed_recorded < ledger_cap {
        proposed_recorded
    } else {
        ledger_cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ledger_committed_clamp(committed: u64, recorded: u64) -> u64 {
    if committed < recorded {
        committed
    } else {
        recorded
    }
}
#[cfg(clean_islands)]
pub use effects_idempotency_ledger_island::{ledger_committed_clamp, ledger_recorded_clamp};

contract_fn! {
    /// Kernel-certified capacity check (`recorded < ledger_cap`), linked via
    /// `clean-kernel-defeq` to `ledger_has_slot_isl`.
    #[must_use]
    pub const fn ledger_has_slot(recorded: u64, ledger_cap: u64) -> bool
    clauses [ensures result == (recorded < ledger_cap)]
    {
        recorded < ledger_cap
    }
}

/// Default maximum effect entries tracked in [`EffectIdempotencyLedger`] (`4096`).
pub const DEFAULT_EFFECT_LEDGER_CAP: usize = 4_096;

/// Lifecycle state of an idempotency-keyed external side effect.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EffectSlotState {
    /// Intent recorded; external confirmation not yet committed.
    InFlight,
    /// Effect completed durably with `receipt_digest`.
    Committed { receipt_digest: [u8; 32] },
}

/// Single entry inside [`EffectIdempotencyLedger`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EffectLedgerEntry {
    /// Agent / workflow step sequence number.
    pub step_seq: u64,
    /// 32-byte SHA-256 idempotency key digest.
    pub key_digest: [u8; 32],
    /// Current state (`InFlight` or `Committed`).
    pub state: EffectSlotState,
}

/// Decision returned by [`EffectIdempotencyLedger::begin_effect`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EffectBeginDecision {
    /// Fresh idempotency key recorded as `InFlight`; caller may execute the side effect.
    ExecuteFresh,
    /// Key was previously left `InFlight` across an interrupted turn; reconcile before re-running.
    ResumeInFlight { step_seq: u64 },
    /// Key already completed; skip execution and replay `receipt_digest`!
    SkipAlreadyCommitted {
        step_seq: u64,
        receipt_digest: [u8; 32],
    },
    /// Ledger reached `ledger_cap` without eviction room (`InFlight` entries are never evicted!).
    LedgerFull,
}

/// Bounded, deterministic side-effect idempotency ledger (`0 mandated`, zero closures).
#[derive(Debug, Clone)]
pub struct EffectIdempotencyLedger {
    ledger_cap: usize,
    committed_count: u64,
    entries: Vec<EffectLedgerEntry>,
}

impl Default for EffectIdempotencyLedger {
    fn default() -> Self {
        Self::new(DEFAULT_EFFECT_LEDGER_CAP)
    }
}

impl EffectIdempotencyLedger {
    /// Construct a new [`EffectIdempotencyLedger`] bounded by `ledger_cap`.
    #[must_use]
    pub fn new(ledger_cap: usize) -> Self {
        let lc_floor = if ledger_cap > 1 { ledger_cap } else { 1 };
        let cap = ledger_recorded_clamp(lc_floor as u64, (DEFAULT_EFFECT_LEDGER_CAP * 16) as u64)
            as usize;
        Self {
            ledger_cap: if cap > 1 { cap } else { 1 },
            committed_count: 0,
            entries: Vec::new(),
        }
    }

    /// Number of recorded effect entries (`<= ledger_cap`).
    #[must_use]
    pub fn recorded_count(&self) -> u64 {
        self.entries.len() as u64
    }

    /// Number of committed effect entries (`<= recorded_count`).
    #[must_use]
    pub const fn committed_count(&self) -> u64 {
        self.committed_count
    }

    fn find_index(&self, key_digest: &[u8; 32]) -> Option<usize> {
        let mut i = 0usize;
        let mut cur: &[EffectLedgerEntry] = &self.entries;
        while let [entry, rest @ ..] = cur {
            if &entry.key_digest == key_digest {
                return Some(i);
            }
            i = i.saturating_add(1);
            cur = rest;
        }
        None
    }

    /// Evict the oldest `Committed` entry (never evicting `InFlight` intents!) when full.
    fn evict_oldest_committed(&mut self) -> bool {
        let mut found = None;
        let mut i = 0usize;
        let mut cur: &[EffectLedgerEntry] = &self.entries;
        while let [entry, rest @ ..] = cur {
            if matches!(entry.state, EffectSlotState::Committed { .. }) {
                found = Some(i);
                break;
            }
            i = i.saturating_add(1);
            cur = rest;
        }
        if let Some(idx) = found {
            if idx < self.entries.len() {
                let mut rebuilt = Vec::new();
                let mut cur_i = 0usize;
                for item in core::mem::take(&mut self.entries) {
                    if cur_i != idx {
                        rebuilt.push(item);
                    }
                    cur_i = cur_i.saturating_add(1);
                }
                self.entries = rebuilt;
                self.committed_count = self.committed_count.saturating_sub(1);
                return true;
            }
        }
        false
    }

    /// Register or deduplicate `(step_seq, key_digest)` before side-effect execution.
    pub fn begin_effect(&mut self, step_seq: u64, key_digest: [u8; 32]) -> EffectBeginDecision {
        if let Some(idx) = self.find_index(&key_digest) {
            if let Some(&entry) = self.entries.get(idx) {
                return match entry.state {
                    EffectSlotState::InFlight => EffectBeginDecision::ResumeInFlight {
                        step_seq: entry.step_seq,
                    },
                    EffectSlotState::Committed { receipt_digest } => {
                        EffectBeginDecision::SkipAlreadyCommitted {
                            step_seq: entry.step_seq,
                            receipt_digest,
                        }
                    }
                };
            }
        }

        if !ledger_has_slot(self.entries.len() as u64, self.ledger_cap as u64)
            && !self.evict_oldest_committed()
        {
            return EffectBeginDecision::LedgerFull;
        }

        self.entries.push(EffectLedgerEntry {
            step_seq,
            key_digest,
            state: EffectSlotState::InFlight,
        });
        let clamped_rec = ledger_recorded_clamp(self.entries.len() as u64, self.ledger_cap as u64);
        self.committed_count = ledger_committed_clamp(self.committed_count, clamped_rec);
        EffectBeginDecision::ExecuteFresh
    }

    /// Transition an `InFlight` key to `Committed { receipt_digest }`. Returns `true` if updated.
    pub fn commit_effect(&mut self, key_digest: &[u8; 32], receipt_digest: [u8; 32]) -> bool {
        let Some(idx) = self.find_index(key_digest) else {
            return false;
        };
        let Some(slot) = self.entries.get_mut(idx) else {
            return false;
        };
        let was_committed = matches!(slot.state, EffectSlotState::Committed { .. });
        slot.state = EffectSlotState::Committed { receipt_digest };
        if !was_committed {
            let raw_c = self.committed_count.saturating_add(1);
            self.committed_count = ledger_committed_clamp(raw_c, self.entries.len() as u64);
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deduplicates_committed_effects_and_preserves_inflight_entries_under_eviction() {
        let mut ledger = EffectIdempotencyLedger::new(2);
        let k1 = [0x01u8; 32];
        let k2 = [0x02u8; 32];
        let k3 = [0x03u8; 32];
        let r1 = [0xAAu8; 32];

        assert_eq!(
            ledger.begin_effect(10, k1),
            EffectBeginDecision::ExecuteFresh
        );
        assert_eq!(
            ledger.begin_effect(10, k1),
            EffectBeginDecision::ResumeInFlight { step_seq: 10 }
        );
        assert!(ledger.commit_effect(&k1, r1));
        assert_eq!(
            ledger.begin_effect(11, k1),
            EffectBeginDecision::SkipAlreadyCommitted {
                step_seq: 10,
                receipt_digest: r1,
            }
        );

        // Leave `k2` InFlight and insert `k3` into cap=2 -> evicts committed `k1`, keeps `k2`!
        assert_eq!(
            ledger.begin_effect(12, k2),
            EffectBeginDecision::ExecuteFresh
        );
        assert_eq!(
            ledger.begin_effect(13, k3),
            EffectBeginDecision::ExecuteFresh
        );
        assert_eq!(ledger.recorded_count(), 2);
        assert_eq!(ledger.committed_count(), 0);
        // Both `k2` and `k3` are now `InFlight`, so a 4th key refuses with `LedgerFull`!
        assert_eq!(
            ledger.begin_effect(14, [0x04u8; 32]),
            EffectBeginDecision::LedgerFull
        );
    }
}
