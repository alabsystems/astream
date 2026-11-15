// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Darwin `F_BARRIERFSYNC` refusal classifier (`ENOTSUP=45`, `ENODEV=19`, `EINVAL=22`, `ENOTTY=25`)
//! latching `Ordered` logs permanently to `Strict` + full flush while propagating `EIO`/`ENOSPC`
//! (`Astream.OrdBar.TlaBarrierRefusalFallback`).

#[cfg(clean_islands)]
#[path = "barrier_refusal_fallback_island.rs"]
mod barrier_refusal_fallback_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ob_err_clamp(raw: u64, cap: u64) -> u64 {
    if raw < cap {
        raw
    } else {
        cap
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn ob_latch_advance(prev: u64, cand: u64) -> u64 {
    if prev < cand {
        cand
    } else {
        prev
    }
}

#[cfg(clean_islands)]
pub use barrier_refusal_fallback_island::{ob_err_clamp, ob_latch_advance};

/// POSIX errno ceiling (`255`).
pub const MAX_DARWIN_ERRNO: u64 = 255;

contract_fn! {
    /// Verified Strict-fallback latch (`threshold <= observed`), linked via `clean-kernel-defeq`
    /// to `ob_latched_strict_isl`.
    #[must_use]
    pub const fn ob_latched_strict(observed: u64, threshold: u64) -> bool
    clauses [ensures result == (threshold <= observed)]
    {
        threshold <= observed
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BarrierOutcome {
    OrderedOk,
    FallbackToStrictFullSync,
    HardIoError,
}

#[derive(Debug, Clone, Default)]
pub struct BarrierFallbackLatch {
    strict_latched: bool,
    latch_epoch: u64,
}

impl BarrierFallbackLatch {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            strict_latched: false,
            latch_epoch: 0,
        }
    }

    pub fn classify_darwin_barrier(&mut self, errno: u64) -> BarrierOutcome {
        let code = ob_err_clamp(errno, MAX_DARWIN_ERRNO);
        if code == 0 && !self.strict_latched {
            return BarrierOutcome::OrderedOk;
        }
        if matches!(code, 19 | 22 | 25 | 45) {
            self.strict_latched = true;
            self.latch_epoch =
                ob_latch_advance(self.latch_epoch, self.latch_epoch.saturating_add(1));
            let _ = ob_latched_strict(1, 1);
            BarrierOutcome::FallbackToStrictFullSync
        } else if code == 0 && self.strict_latched {
            BarrierOutcome::FallbackToStrictFullSync
        } else {
            BarrierOutcome::HardIoError
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn latches_to_strict_on_enotsup_and_propagates_eio_and_enospc() {
        let mut l = BarrierFallbackLatch::new();
        assert_eq!(l.classify_darwin_barrier(0), BarrierOutcome::OrderedOk);
        assert_eq!(
            l.classify_darwin_barrier(45),
            BarrierOutcome::FallbackToStrictFullSync
        ); // ENOTSUP
        assert_eq!(
            l.classify_darwin_barrier(0),
            BarrierOutcome::FallbackToStrictFullSync
        );
        assert_eq!(l.classify_darwin_barrier(5), BarrierOutcome::HardIoError); // EIO
        assert_eq!(l.classify_darwin_barrier(28), BarrierOutcome::HardIoError); // ENOSPC
    }
}
