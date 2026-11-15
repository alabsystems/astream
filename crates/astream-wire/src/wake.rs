// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

#![allow(clippy::manual_is_ascii_check)]

//! Fabric wake priority algebra, sender-demotion rules, and per-recipient window-budget
//! coalescing (`DESIGN-aterm-fabric.md` §4.2, §5.6, T9).
//!
//! ## Overview
//!
//! 1. **[`WakeClass`]**: Closed priority lattice over the nine `in`-lane message kinds
//!    (`control > ask > task > answer > report > ack > expired > undeliverable > note`,
//!    `DESIGN-aterm-fabric` §4.2, §5.6) plus the deterministic receiver-side sender
//!    demotion rule ([`WakeClass::classify_for_sender`]: relayed `via=`, stray replies,
//!    and unlisted `task`/`control` demote to `note`).
//! 2. **[`WakeBudget`]**: Sliding-window per-recipient wake ceiling (`<n>/<unit>`, default
//!    `6/min`, capped at [`MAX_WAKE_WINDOW_STAMPS`] stamps for zero-allocation stack storage).
//! 3. **[`SessionWakeLedger`]**: Zero-allocation per-recipient coalescer and sliding-window
//!    rate limiter backed by Clean-origin [`wake_rank_max`], [`wake_charge_clamp`], and
//!    [`wake_within_budget`] (`Astream.Wire.TlaWakeBudget`). Guarantees at most one wake
//!    per pending batch (`emittedInBatch <= 1`) and at most `budget.max_wakes` non-exempt
//!    wakes per sliding `window_ms` (`usedWakes <= maxBudget`).

use crate::receipt::monotone_clock_tick;
use crate::Offset;
use core::fmt;

#[cfg(clean_islands)]
#[path = "wake_island.rs"]
mod wake_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{wake_charge_clamp, wake_rank_max};
#[cfg(clean_islands)]
pub use wake_island::{wake_charge_clamp, wake_rank_max};

contract_fn! {
    /// Kernel-certified check that `used` wakes in the active window is strictly below
    /// `budget` (`used < budget`), linked via `clean-kernel-defeq` to `wake_within_budget_isl`.
    #[must_use]
    pub const fn wake_within_budget(used: u64, budget: u64) -> bool
    clauses [ensures result == (used < budget)]
    {
        used < budget
    }
}

/// Maximum `max_wakes` supported by the zero-allocation [`SessionWakeLedger`] stamp ring.
pub const MAX_WAKE_WINDOW_STAMPS: usize = 64;

const fn bytes_eq(mut a: &[u8], mut b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    while let (&[x, ref at @ ..], &[y, ref bt @ ..]) = (a, b) {
        if x != y {
            return false;
        }
        a = at;
        b = bt;
    }
    true
}

const fn parse_leading_digits(mut bytes: &[u8]) -> Option<(Option<u64>, &[u8])> {
    let mut acc = 0u64;
    let mut has_digit = false;
    while let &[b, ref tail @ ..] = bytes {
        if !matches!(b, b'0'..=b'9') {
            break;
        }
        let digit = b.saturating_sub(b'0') as u64;
        let Some(mul) = acc.checked_mul(10) else {
            return None;
        };
        let Some(next) = mul.checked_add(digit) else {
            return None;
        };
        acc = next;
        has_digit = true;
        bytes = tail;
    }
    let prefix = if has_digit { Some(acc) } else { None };
    Some((prefix, bytes))
}

const fn parse_window_ms(rhs: &[u8]) -> Option<u64> {
    let Some((opt_k, unit)) = parse_leading_digits(rhs) else {
        return None;
    };
    match opt_k {
        None => {
            if bytes_eq(unit, b"min") || bytes_eq(unit, b"m") {
                Some(60_000)
            } else if bytes_eq(unit, b"s") || bytes_eq(unit, b"sec") {
                Some(1_000)
            } else {
                None
            }
        }
        Some(k) => {
            if bytes_eq(unit, b"min") || bytes_eq(unit, b"m") {
                k.checked_mul(60_000)
            } else if bytes_eq(unit, b"ms") {
                Some(k)
            } else if bytes_eq(unit, b"s") {
                k.checked_mul(1_000)
            } else {
                None
            }
        }
    }
}

const fn parse_u64_before_slash(mut bytes: &[u8]) -> Option<(u64, &[u8])> {
    let mut acc = 0u64;
    let mut has_digit = false;
    while let &[b, ref tail @ ..] = bytes {
        if b == b'/' {
            if !has_digit {
                return None;
            }
            return Some((acc, tail));
        }
        if !matches!(b, b'0'..=b'9') {
            return None;
        }
        let digit = b.saturating_sub(b'0') as u64;
        let Some(mul) = acc.checked_mul(10) else {
            return None;
        };
        let Some(next) = mul.checked_add(digit) else {
            return None;
        };
        acc = next;
        has_digit = true;
        bytes = tail;
    }
    None
}

/// Priority class of an `in`-lane fabric message (`DESIGN-aterm-fabric.md` §4.2, §5.6).
///
/// Ordered from lowest (`Note = 0`, silent by default) to highest (`Control = 8`):
/// `control > ask > task > answer > report > ack > expired > undeliverable > note`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum WakeClass {
    /// Passive informational note or demoted delivery (`rank == 0`; never wakes by default).
    Note = 0,
    /// Bridge-recorded undeliverable diagnostic (`rank == 1`).
    Undeliverable = 1,
    /// Deadline-expiry receipt (`rank == 2`).
    Expired = 2,
    /// Disposition acknowledgment (`rank == 3`).
    Ack = 3,
    /// Asynchronous task completion report (`rank == 4`).
    Report = 4,
    /// Direct answer to an earlier `ask` (`rank == 5`).
    Answer = 5,
    /// Delegated work item (`rank == 6`).
    Task = 6,
    /// Direct question awaiting an answer (`rank == 7`).
    Ask = 7,
    /// Control-plane handoff or directive (`rank == 8`, highest priority).
    Control = 8,
}

impl WakeClass {
    /// Maximum numeric rank across [`Self::ALL`] (`Self::Control.rank() == 8`).
    pub const MAX_RANK: u64 = 8;

    /// All nine `in`-lane kinds in descending priority order (`control ..= note`).
    pub const ALL: [Self; 9] = [
        Self::Control,
        Self::Ask,
        Self::Task,
        Self::Answer,
        Self::Report,
        Self::Ack,
        Self::Expired,
        Self::Undeliverable,
        Self::Note,
    ];

    /// Numeric priority rank (`0..=8`).
    #[must_use]
    pub const fn rank(self) -> u64 {
        self as u64
    }

    /// Reconstruct a [`WakeClass`] from its clamped rank (`0..=8`).
    #[must_use]
    pub const fn from_rank(rank: u64) -> Self {
        match rank {
            0 => Self::Note,
            1 => Self::Undeliverable,
            2 => Self::Expired,
            3 => Self::Ack,
            4 => Self::Report,
            5 => Self::Answer,
            6 => Self::Task,
            7 => Self::Ask,
            _ => Self::Control,
        }
    }

    /// Coalesce two classes to the higher-priority one via Clean-origin [`wake_rank_max`].
    #[must_use]
    pub const fn coalesce(self, other: Self) -> Self {
        Self::from_rank(wake_rank_max(self.rank(), other.rank()))
    }

    /// Whether this class ends a parked `await inbox` / triggers a wake by default
    /// (`DESIGN-aterm-fabric.md` §5.6: every class strictly above `Note`).
    #[must_use]
    pub const fn wakes_by_default(self) -> bool {
        self.rank() > 0
    }

    /// Canonical wire segment spelling (`control`, `ask`, ..., `note`).
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Control => "control",
            Self::Ask => "ask",
            Self::Task => "task",
            Self::Answer => "answer",
            Self::Report => "report",
            Self::Ack => "ack",
            Self::Expired => "expired",
            Self::Undeliverable => "undeliverable",
            Self::Note => "note",
        }
    }

    /// Parse an `in`-lane `<kind>` segment byte slice into its [`WakeClass`].
    #[must_use]
    pub const fn parse_bytes(s: &[u8]) -> Option<Self> {
        let mut rest: &[Self] = &Self::ALL;
        while let &[cls, ref tail @ ..] = rest {
            if bytes_eq(s, cls.as_str().as_bytes()) {
                return Some(cls);
            }
            rest = tail;
        }
        None
    }

    /// Parse an `in`-lane `<kind>` segment string into its [`WakeClass`].
    #[must_use]
    pub const fn parse(s: &str) -> Option<Self> {
        Self::parse_bytes(s.as_bytes())
    }

    /// Apply receiver-side sender-trust demotion (`DESIGN-aterm-fabric.md` §5.6 `classify_delivery`):
    /// - Any relayed (`relayed_via == true`) delivery demotes to [`Self::Note`].
    /// - Any stray reply (`stray_reply == true` on `Answer`, `Report`, `Ack`, or `Expired`)
    ///   demotes to [`Self::Note`].
    /// - An unlisted principal (`!sender_accepted`) sending `Task` or `Control` demotes
    ///   to [`Self::Note`].
    #[must_use]
    pub const fn classify_for_sender(
        self,
        sender_accepted: bool,
        relayed_via: bool,
        stray_reply: bool,
    ) -> Self {
        if relayed_via {
            return Self::Note;
        }
        if stray_reply
            && matches!(
                self,
                Self::Answer | Self::Report | Self::Ack | Self::Expired
            )
        {
            return Self::Note;
        }
        if !sender_accepted && matches!(self, Self::Task | Self::Control) {
            return Self::Note;
        }
        self
    }
}

impl fmt::Display for WakeClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Sliding-window per-recipient wake budget (`<n>/<unit>`, `DESIGN-aterm-fabric.md` §5.6).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WakeBudget {
    /// Maximum non-exempt wakes permitted within `window_ms` (`1..=MAX_WAKE_WINDOW_STAMPS`).
    pub max_wakes: u32,
    /// Sliding window width in milliseconds (`> 0`).
    pub window_ms: u64,
}

impl WakeBudget {
    /// Default fabric wake budget (`6/min`: 6 wakes per 60,000 ms, §5.6).
    pub const DEFAULT: Self = Self {
        max_wakes: 6,
        window_ms: 60_000,
    };

    /// Construct a validated [`WakeBudget`], returning `None` if `max_wakes == 0`,
    /// `max_wakes > MAX_WAKE_WINDOW_STAMPS`, or `window_ms == 0`.
    #[must_use]
    pub const fn new(max_wakes: u32, window_ms: u64) -> Option<Self> {
        if max_wakes == 0 || (max_wakes as usize) > MAX_WAKE_WINDOW_STAMPS || window_ms == 0 {
            return None;
        }
        Some(Self {
            max_wakes,
            window_ms,
        })
    }

    /// Parse `<n>/<unit>` (`"6/min"`, `"6/m"`, `"10/60s"`, `"12/2min"`, `"5/1000ms"`).
    #[must_use]
    pub const fn parse_bytes(bytes: &[u8]) -> Option<Self> {
        let Some((n64, rhs)) = parse_u64_before_slash(bytes) else {
            return None;
        };
        if n64 == 0 || n64 > (MAX_WAKE_WINDOW_STAMPS as u64) {
            return None;
        }
        let max_wakes = n64 as u32;
        let Some(window_ms) = parse_window_ms(rhs) else {
            return None;
        };
        Self::new(max_wakes, window_ms)
    }

    /// Parse `<n>/<unit>` from a string slice.
    #[must_use]
    pub const fn parse(spec: &str) -> Option<Self> {
        Self::parse_bytes(spec.as_bytes())
    }
}

/// Outcome of evaluating a pending recipient batch against [`SessionWakeLedger`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WakeDecision {
    /// No deliveries have arrived in the current batch.
    EmptyBatch,
    /// Only `note`-level deliveries arrived in the current batch (`!wakes_by_default`).
    SilentNote {
        /// Number of `note` deliveries coalesced in this batch.
        pending_count: u32,
    },
    /// This pending batch already emitted its single coalesced wake (`emittedInBatch == 1`).
    AlreadyWokenInBatch {
        /// Highest priority class observed in the batch so far.
        highest: WakeClass,
        /// Total deliveries observed in the batch so far.
        pending_count: u32,
    },
    /// Emit one coalesced wake for the recipient.
    Wake {
        /// Highest priority class across all deliveries in the pending batch.
        highest: WakeClass,
        /// Number of deliveries coalesced into this single wake.
        pending_count: u32,
        /// Highest log offset observed in the batch.
        newest_offset: Offset,
        /// Non-exempt wakes charged inside the current sliding window after this wake.
        used_in_window: u32,
    },
    /// Suppressed by the sliding-window wake budget (`used_in_window == budget.max_wakes`).
    Throttled {
        /// Highest priority class waiting in the suppressed batch.
        highest: WakeClass,
        /// Number of deliveries waiting in the suppressed batch.
        pending_count: u32,
        /// Milliseconds until the oldest charged wake exits the sliding window.
        retry_after_ms: u64,
    },
}

/// Zero-allocation per-recipient wake coalescer and sliding-window budget ledger.
#[derive(Debug, Clone)]
pub struct SessionWakeLedger {
    budget: WakeBudget,
    now_ms: u64,
    stamps_ms: [u64; MAX_WAKE_WINDOW_STAMPS],
    stamp_len: usize,
    pending_count: u32,
    highest_class: Option<WakeClass>,
    newest_offset: Option<Offset>,
    batch_woken: bool,
    exempt_pending: bool,
}

impl SessionWakeLedger {
    /// Create a fresh ledger governed by `budget`.
    #[must_use]
    pub const fn new(budget: WakeBudget) -> Self {
        Self {
            budget,
            now_ms: 0,
            stamps_ms: [0u64; MAX_WAKE_WINDOW_STAMPS],
            stamp_len: 0,
            pending_count: 0,
            highest_class: None,
            newest_offset: None,
            batch_woken: false,
            exempt_pending: false,
        }
    }

    /// Configured [`WakeBudget`].
    #[must_use]
    pub const fn budget(&self) -> WakeBudget {
        self.budget
    }

    /// Current monotone clock (`ms`) of this ledger.
    #[must_use]
    pub const fn now_ms(&self) -> u64 {
        self.now_ms
    }

    /// Number of non-exempt wakes currently active in the sliding window.
    #[must_use]
    pub const fn used_in_window(&self) -> u32 {
        self.stamp_len as u32
    }

    /// Highest [`WakeClass`] observed in the current undrained batch, if any.
    #[must_use]
    pub const fn pending_highest(&self) -> Option<WakeClass> {
        self.highest_class
    }

    /// Number of deliveries observed in the current undrained batch.
    #[must_use]
    pub const fn pending_count(&self) -> u32 {
        self.pending_count
    }

    /// Observe one inbound delivery at `offset` with effective `class` (after
    /// [`WakeClass::classify_for_sender`] demotion) and whether the sender is budget-exempt.
    pub fn observe(&mut self, offset: Offset, class: WakeClass, sender_exempt: bool) {
        self.pending_count = self.pending_count.saturating_add(1);
        self.highest_class = Some(match self.highest_class {
            Some(cur) => cur.coalesce(class),
            None => class,
        });
        self.newest_offset = Some(match self.newest_offset {
            Some(cur) if cur.0 >= offset.0 => cur,
            _ => offset,
        });
        if sender_exempt && class.wakes_by_default() {
            self.exempt_pending = true;
        }
    }

    fn trim_window(&mut self, sample_ms: u64) {
        self.now_ms = monotone_clock_tick(self.now_ms, sample_ms);
        let cap = (self.budget.max_wakes as usize).min(MAX_WAKE_WINDOW_STAMPS);
        let len = self.stamp_len.min(cap);
        let mut keep_from = 0usize;
        while keep_from < len {
            let Some(&stamp) = self.stamps_ms.get(keep_from) else {
                break;
            };
            let elapsed = self.now_ms.saturating_sub(stamp);
            if elapsed < self.budget.window_ms {
                break;
            }
            keep_from = keep_from.saturating_add(1);
        }
        if keep_from > 0 {
            let kept = len.saturating_sub(keep_from);
            let mut dst = 0usize;
            while dst < kept {
                let src = keep_from.saturating_add(dst);
                if let Some(&val) = self.stamps_ms.get(src) {
                    if let Some(slot) = self.stamps_ms.get_mut(dst) {
                        *slot = val;
                    }
                }
                dst = dst.saturating_add(1);
            }
            let clamped = wake_charge_clamp(kept as u64, self.budget.max_wakes as u64) as usize;
            self.stamp_len = clamped.min(MAX_WAKE_WINDOW_STAMPS);
        } else {
            self.stamp_len = len;
        }
    }

    /// Evaluate the current pending batch at `sample_ms`, emitting at most one wake per
    /// pending batch and charging the sliding-window budget when non-exempt.
    pub fn flush_batch(&mut self, sample_ms: u64) -> WakeDecision {
        self.trim_window(sample_ms);
        let (Some(highest), Some(newest_offset)) = (self.highest_class, self.newest_offset) else {
            return WakeDecision::EmptyBatch;
        };
        if !highest.wakes_by_default() {
            return WakeDecision::SilentNote {
                pending_count: self.pending_count,
            };
        }
        if self.batch_woken {
            return WakeDecision::AlreadyWokenInBatch {
                highest,
                pending_count: self.pending_count,
            };
        }
        let max_b = self.budget.max_wakes as u64;
        let used = self.stamp_len as u64;
        if !self.exempt_pending && !wake_within_budget(used, max_b) {
            let oldest = match self.stamps_ms {
                [first, ..] if self.stamp_len > 0 => first,
                _ => self.now_ms,
            };
            let elapsed = self.now_ms.saturating_sub(oldest);
            let retry_after_ms = self.budget.window_ms.saturating_sub(elapsed);
            return WakeDecision::Throttled {
                highest,
                pending_count: self.pending_count,
                retry_after_ms,
            };
        }
        if !self.exempt_pending {
            let idx = self.stamp_len;
            if let Some(slot) = self.stamps_ms.get_mut(idx) {
                *slot = self.now_ms;
                let next_used = wake_charge_clamp((idx as u64).saturating_add(1), max_b) as usize;
                self.stamp_len = next_used.min(MAX_WAKE_WINDOW_STAMPS);
            }
        }
        self.batch_woken = true;
        WakeDecision::Wake {
            highest,
            pending_count: self.pending_count,
            newest_offset,
            used_in_window: self.stamp_len as u32,
        }
    }

    /// Clear the pending batch once the recipient drains its inbox or resumes its turn,
    /// preserving the sliding-window wake history.
    pub fn reset_batch(&mut self) {
        self.pending_count = 0;
        self.highest_class = None;
        self.newest_offset = None;
        self.batch_woken = false;
        self.exempt_pending = false;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wake_class_priority_and_sender_demotion_match_fabric_spec() {
        assert!(WakeClass::Control > WakeClass::Ask);
        assert!(WakeClass::Ask > WakeClass::Task);
        assert!(WakeClass::Task > WakeClass::Answer);
        assert!(WakeClass::Answer > WakeClass::Report);
        assert!(WakeClass::Report > WakeClass::Ack);
        assert!(WakeClass::Ack > WakeClass::Expired);
        assert!(WakeClass::Expired > WakeClass::Undeliverable);
        assert!(WakeClass::Undeliverable > WakeClass::Note);
        assert!(!WakeClass::Note.wakes_by_default());
        assert!(WakeClass::Undeliverable.wakes_by_default());

        for cls in WakeClass::ALL {
            assert_eq!(WakeClass::parse(cls.as_str()), Some(cls));
            assert_eq!(cls.classify_for_sender(true, true, false), WakeClass::Note);
        }
        assert_eq!(
            WakeClass::Task.classify_for_sender(false, false, false),
            WakeClass::Note
        );
        assert_eq!(
            WakeClass::Control.classify_for_sender(false, false, false),
            WakeClass::Note
        );
        assert_eq!(
            WakeClass::Ask.classify_for_sender(false, false, false),
            WakeClass::Ask
        );
        assert_eq!(
            WakeClass::Answer.classify_for_sender(true, false, true),
            WakeClass::Note
        );
    }

    #[test]
    fn wake_budget_parses_units_and_ledger_coalesces_and_throttles() {
        assert_eq!(WakeBudget::parse("6/min"), Some(WakeBudget::DEFAULT));
        assert_eq!(WakeBudget::parse("6/m"), Some(WakeBudget::DEFAULT));
        assert_eq!(
            WakeBudget::parse("4/sec"),
            Some(WakeBudget {
                max_wakes: 4,
                window_ms: 1_000,
            })
        );
        assert_eq!(
            WakeBudget::parse("4/s"),
            Some(WakeBudget {
                max_wakes: 4,
                window_ms: 1_000,
            })
        );
        assert_eq!(
            WakeBudget::parse("12/2min"),
            Some(WakeBudget {
                max_wakes: 12,
                window_ms: 120_000,
            })
        );
        assert_eq!(
            WakeBudget::parse("3/2m"),
            Some(WakeBudget {
                max_wakes: 3,
                window_ms: 120_000,
            })
        );
        assert_eq!(
            WakeBudget::parse("5/1000ms"),
            Some(WakeBudget {
                max_wakes: 5,
                window_ms: 1_000,
            })
        );
        assert_eq!(
            WakeBudget::parse("2/10s"),
            Some(WakeBudget {
                max_wakes: 2,
                window_ms: 10_000
            })
        );
        assert_eq!(WakeBudget::parse("0/min"), None);
        assert_eq!(WakeBudget::parse("999/min"), None);
        assert_eq!(WakeBudget::parse("6/ms"), None);
        assert_eq!(WakeBudget::parse("6/10sec"), None);
        assert_eq!(WakeBudget::parse("6/0s"), None);

        let mut ledger = SessionWakeLedger::new(WakeBudget::parse("2/10s").unwrap());
        ledger.observe(Offset(10), WakeClass::Ack, false);
        ledger.observe(Offset(12), WakeClass::Ask, false);
        assert_eq!(
            ledger.flush_batch(1_000),
            WakeDecision::Wake {
                highest: WakeClass::Ask,
                pending_count: 2,
                newest_offset: Offset(12),
                used_in_window: 1,
            }
        );
        assert_eq!(
            ledger.flush_batch(1_050),
            WakeDecision::AlreadyWokenInBatch {
                highest: WakeClass::Ask,
                pending_count: 2,
            }
        );

        ledger.reset_batch();
        ledger.observe(Offset(15), WakeClass::Report, false);
        assert!(matches!(
            ledger.flush_batch(2_000),
            WakeDecision::Wake {
                used_in_window: 2,
                ..
            }
        ));

        ledger.reset_batch();
        ledger.observe(Offset(18), WakeClass::Task, false);
        assert_eq!(
            ledger.flush_batch(3_000),
            WakeDecision::Throttled {
                highest: WakeClass::Task,
                pending_count: 1,
                retry_after_ms: 8_000,
            }
        );

        // Exempt sender (e.g. human operator) still wakes even while budget is full!
        ledger.observe(Offset(19), WakeClass::Control, true);
        assert!(matches!(
            ledger.flush_batch(3_100),
            WakeDecision::Wake {
                highest: WakeClass::Control,
                used_in_window: 2,
                ..
            }
        ));

        // Sliding window advances past the first stamp at 11_000 ms.
        ledger.reset_batch();
        ledger.observe(Offset(20), WakeClass::Ask, false);
        assert!(matches!(
            ledger.flush_batch(11_000),
            WakeDecision::Wake {
                used_in_window: 2,
                ..
            }
        ));
    }
}
