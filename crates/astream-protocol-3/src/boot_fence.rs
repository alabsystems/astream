// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Pure, Clean-verified 16-byte kernel boot-session & monotone generation fence
//! (`Astream.Engine.TlaBootEpochFence`) for Ordered-tier page-cache recovery and
//! `aterm` supervisor / release-publisher `fence-boot` leases.
//!
//! Across `aterm` (`aterm-link`, `aterm-agent`, `aterm-caffeine`, `aterm-gui`,
//! `aterm-uds`, `aterm-release`) and `astream`'s Ordered-durability logs, unflushed
//! page-cache state and process-tree leases remain valid **only** when:
//! 1. Both the recorded boot id and the live kernel boot id are `Some([u8; 16])` and
//!    constant-time equal (process crash/restart preserves the kernel page cache;
//!    reboot, power loss, or an unknown `None` boot id invalidates it), AND
//! 2. The recorded lease generation is at least the monotone fence epoch
//!    (`boot_epoch_fresh(recorded_epoch, fence_epoch)`).
//!
//! Whenever boot continuity fails, [`BootFence::reconcile_ordered_heads`] fail-closed
//! rolls back the trusted log head from `page_cache_head` to
//! `boot_unflushed_clamp(page_cache_head, durable_fsync_head)` and promotes the
//! recovery action to [`OrderedRecoveryAction::RollbackToDurableAndFullSync`].

#[cfg(clean_islands)]
#[path = "boot_fence_island.rs"]
mod boot_fence_island;

#[cfg(not(clean_islands))]
#[must_use]
pub const fn boot_fence_epoch_advance(cur_epoch: u64, cand_epoch: u64) -> u64 {
    if cur_epoch < cand_epoch {
        cand_epoch
    } else {
        cur_epoch
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn boot_unflushed_clamp(unflushed: u64, committed: u64) -> u64 {
    if unflushed < committed {
        unflushed
    } else {
        committed
    }
}
#[cfg(clean_islands)]
pub use boot_fence_island::{boot_fence_epoch_advance, boot_unflushed_clamp};

/// Binary wire magic (`"ABF1"`) for a 36-byte serialized [`BootLeaseRecord`].
pub const BOOT_LEASE_MAGIC: [u8; 4] = *b"ABF1";

/// Fixed encoded length of a [`BootLeaseRecord`]: `4 (magic) + 1 (has_boot) + 3 (pad) + 16 (boot_id) + 8 (epoch) + 8 (durable_head) = 40` bytes.
pub const BOOT_LEASE_WIRE_LEN: usize = 40;

contract_fn! {
    /// Kernel-certified freshness predicate checking `recorded_epoch >= fence_epoch`.
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `boot_epoch_fresh_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn boot_epoch_fresh(recorded_epoch: u64, fence_epoch: u64) -> bool
    clauses [ensures result == (fence_epoch <= recorded_epoch)]
    {
        fence_epoch <= recorded_epoch
    }
}

/// Constant-time 16-byte boot-UUID equality check (zero early-exit branches).
#[must_use]
pub const fn boot_id_ct_eq(a: &[u8; 16], b: &[u8; 16]) -> bool {
    let d0 = (a[0] ^ b[0]) | (a[1] ^ b[1]) | (a[2] ^ b[2]) | (a[3] ^ b[3]);
    let d1 = (a[4] ^ b[4]) | (a[5] ^ b[5]) | (a[6] ^ b[6]) | (a[7] ^ b[7]);
    let d2 = (a[8] ^ b[8]) | (a[9] ^ b[9]) | (a[10] ^ b[10]) | (a[11] ^ b[11]);
    let d3 = (a[12] ^ b[12]) | (a[13] ^ b[13]) | (a[14] ^ b[14]) | (a[15] ^ b[15]);
    (d0 | d1 | d2 | d3) == 0
}

/// Verdict when evaluating a recorded boot-bound lease against the live kernel boot id
/// and current monotone [`BootFence`] epoch.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BootLeaseVerdict {
    /// Both boot ids are known, match byte-for-byte, and `recorded_epoch >= fence_epoch`.
    SameBootValid,
    /// Either the recorded or live boot id is `None` (cannot vouch for kernel continuity).
    UnknownBootFailClosed,
    /// Live kernel boot id differs from recorded boot id (reboot or power loss intervened).
    RebootDetected,
    /// Same kernel boot, but `recorded_epoch < fence_epoch` (fenced out by newer owner).
    StaleEpochFenced,
}

/// Recovery decision for an Ordered-durability log that recorded both a full-fsync
/// `durable_head` and an `F_BARRIERFSYNC` / page-cache `page_cache_head`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OrderedRecoveryAction {
    /// Kernel page cache survived intact across process restart; `trusted_head` keeps
    /// the barrier-ordered head (`clamped <= page_cache_head`).
    RetainPageCacheHead { trusted_head: u64 },
    /// Kernel rebooted, boot id is unavailable, or epoch was fenced; roll back
    /// `trusted_head` to `min(page_cache_head, durable_head)` and require a full `fsync`.
    RollbackToDurableAndFullSync { trusted_head: u64 },
}

/// Fixed-size 40-byte durable boot-lease record suitable for atomic state-file writes
/// (`aterm-release` `fence-boot`, `aterm-agent` tape header, or `FileLog` sidecar).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BootLeaseRecord {
    pub boot_id: Option<[u8; 16]>,
    pub epoch: u64,
    pub durable_head: u64,
}

impl BootLeaseRecord {
    /// Encode to a deterministic 40-byte `"ABF1"` frame.
    #[must_use]
    pub const fn encode(&self) -> [u8; BOOT_LEASE_WIRE_LEN] {
        let (flag, b) = match self.boot_id {
            Some(id) => (1u8, id),
            None => (0u8, [0u8; 16]),
        };
        let ep = self.epoch.to_le_bytes();
        let dh = self.durable_head.to_le_bytes();
        [
            BOOT_LEASE_MAGIC[0],
            BOOT_LEASE_MAGIC[1],
            BOOT_LEASE_MAGIC[2],
            BOOT_LEASE_MAGIC[3],
            flag,
            0,
            0,
            0,
            b[0],
            b[1],
            b[2],
            b[3],
            b[4],
            b[5],
            b[6],
            b[7],
            b[8],
            b[9],
            b[10],
            b[11],
            b[12],
            b[13],
            b[14],
            b[15],
            ep[0],
            ep[1],
            ep[2],
            ep[3],
            ep[4],
            ep[5],
            ep[6],
            ep[7],
            dh[0],
            dh[1],
            dh[2],
            dh[3],
            dh[4],
            dh[5],
            dh[6],
            dh[7],
        ]
    }

    /// Decode a 40-byte `"ABF1"` frame, failing closed on bad magic, reserved bytes, or
    /// non-canonical `has_boot` flag (`0` with non-zero UUID bytes, or `> 1`).
    pub fn decode(bytes: &[u8]) -> Result<Self, &'static str> {
        let &[m0, m1, m2, m3, flag, r0, r1, r2, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, e0, e1, e2, e3, e4, e5, e6, e7, d0, d1, d2, d3, d4, d5, d6, d7] =
            bytes
        else {
            return Err("invalid boot lease length");
        };
        if [m0, m1, m2, m3] != BOOT_LEASE_MAGIC {
            return Err("invalid boot lease magic");
        }
        if [r0, r1, r2] != [0, 0, 0] {
            return Err("non-zero reserved boot lease bytes");
        }
        let raw_id = [
            b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
        ];
        let boot_id = match flag {
            0 => {
                if !boot_id_ct_eq(&raw_id, &[0u8; 16]) {
                    return Err("absent boot_id carries non-zero bytes");
                }
                None
            }
            1 => Some(raw_id),
            _ => return Err("invalid boot_id presence flag"),
        };
        Ok(Self {
            boot_id,
            epoch: u64::from_le_bytes([e0, e1, e2, e3, e4, e5, e6, e7]),
            durable_head: u64::from_le_bytes([d0, d1, d2, d3, d4, d5, d6, d7]),
        })
    }
}

/// Monotone boot-session & generation fence state machine.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BootFence {
    live_boot_id: Option<[u8; 16]>,
    fence_epoch: u64,
}

impl BootFence {
    /// Construct a fence anchored to `live_boot_id` at `initial_epoch`.
    #[must_use]
    pub const fn new(live_boot_id: Option<[u8; 16]>, initial_epoch: u64) -> Self {
        Self {
            live_boot_id,
            fence_epoch: initial_epoch,
        }
    }

    /// Current monotone fence epoch.
    #[must_use]
    pub const fn fence_epoch(&self) -> u64 {
        self.fence_epoch
    }

    /// Current live kernel boot session UUID (`None` if platform cannot vouch for boot).
    #[must_use]
    pub const fn live_boot_id(&self) -> Option<[u8; 16]> {
        self.live_boot_id
    }

    /// Monotonically advance `fence_epoch` to `max(self.fence_epoch, candidate_epoch)`.
    pub fn advance_epoch(&mut self, candidate_epoch: u64) -> u64 {
        self.fence_epoch = boot_fence_epoch_advance(self.fence_epoch, candidate_epoch);
        self.fence_epoch
    }

    /// Observe a fresh kernel `boot_session` reading; if the boot changed or became
    /// unknown, bumps `fence_epoch` by 1 (saturating) so prior boot leases cannot
    /// accidentally match a future epoch check.
    pub fn observe_live_boot(&mut self, observed_boot: Option<[u8; 16]>) -> bool {
        let same = match (self.live_boot_id, observed_boot) {
            (Some(a), Some(b)) => boot_id_ct_eq(&a, &b),
            _ => false,
        };
        self.live_boot_id = observed_boot;
        if !same {
            let next = self.fence_epoch.saturating_add(1);
            self.fence_epoch = boot_fence_epoch_advance(self.fence_epoch, next);
        }
        same
    }

    /// Evaluate a recorded [`BootLeaseRecord`] against `self`.
    #[must_use]
    pub const fn evaluate(&self, recorded: &BootLeaseRecord) -> BootLeaseVerdict {
        let (Some(live), Some(rec)) = (self.live_boot_id, recorded.boot_id) else {
            return BootLeaseVerdict::UnknownBootFailClosed;
        };
        if !boot_id_ct_eq(&live, &rec) {
            return BootLeaseVerdict::RebootDetected;
        }
        if !boot_epoch_fresh(recorded.epoch, self.fence_epoch) {
            return BootLeaseVerdict::StaleEpochFenced;
        }
        BootLeaseVerdict::SameBootValid
    }

    /// Decide the safe recovery head for an Ordered-durability log given `recorded`
    /// metadata and its barrier-ordered `page_cache_head`.
    #[must_use]
    pub const fn reconcile_ordered_heads(
        &self,
        recorded: &BootLeaseRecord,
        page_cache_head: u64,
    ) -> OrderedRecoveryAction {
        match self.evaluate(recorded) {
            BootLeaseVerdict::SameBootValid => {
                let trusted_head = if page_cache_head < recorded.durable_head {
                    recorded.durable_head
                } else {
                    page_cache_head
                };
                OrderedRecoveryAction::RetainPageCacheHead { trusted_head }
            }
            BootLeaseVerdict::UnknownBootFailClosed
            | BootLeaseVerdict::RebootDetected
            | BootLeaseVerdict::StaleEpochFenced => {
                let trusted_head = boot_unflushed_clamp(page_cache_head, recorded.durable_head);
                OrderedRecoveryAction::RollbackToDurableAndFullSync { trusted_head }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn same_boot_retains_page_cache_while_reboot_unknown_and_stale_epoch_rollback() {
        let boot_a = [0x11u8; 16];
        let boot_b = [0x22u8; 16];
        let mut fence = BootFence::new(Some(boot_a), 5);

        let valid = BootLeaseRecord {
            boot_id: Some(boot_a),
            epoch: 5,
            durable_head: 120,
        };
        assert_eq!(fence.evaluate(&valid), BootLeaseVerdict::SameBootValid);
        assert_eq!(
            fence.reconcile_ordered_heads(&valid, 145),
            OrderedRecoveryAction::RetainPageCacheHead { trusted_head: 145 }
        );

        // Advance fence epoch -> prior lease is fenced out even on same boot.
        assert_eq!(fence.advance_epoch(6), 6);
        assert_eq!(fence.evaluate(&valid), BootLeaseVerdict::StaleEpochFenced);
        assert_eq!(
            fence.reconcile_ordered_heads(&valid, 145),
            OrderedRecoveryAction::RollbackToDurableAndFullSync { trusted_head: 120 }
        );

        // Reboot detected -> roll back to durable_head.
        assert!(!fence.observe_live_boot(Some(boot_b)));
        let fresh_epoch_old_boot = BootLeaseRecord {
            boot_id: Some(boot_a),
            epoch: fence.fence_epoch(),
            durable_head: 120,
        };
        assert_eq!(
            fence.evaluate(&fresh_epoch_old_boot),
            BootLeaseVerdict::RebootDetected
        );
        assert_eq!(
            fence.reconcile_ordered_heads(&fresh_epoch_old_boot, 145),
            OrderedRecoveryAction::RollbackToDurableAndFullSync { trusted_head: 120 }
        );

        // Unknown boot -> fail closed.
        let unknown_fence = BootFence::new(None, 0);
        assert_eq!(
            unknown_fence.evaluate(&valid),
            BootLeaseVerdict::UnknownBootFailClosed
        );
    }

    #[test]
    fn wire_codec_roundtrips_and_rejects_noncanonical_absent_boot() {
        let some_rec = BootLeaseRecord {
            boot_id: Some([0xAB; 16]),
            epoch: 42,
            durable_head: 9_001,
        };
        let bytes = some_rec.encode();
        assert_eq!(BootLeaseRecord::decode(&bytes).unwrap(), some_rec);

        let none_rec = BootLeaseRecord {
            boot_id: None,
            epoch: 7,
            durable_head: 0,
        };
        let mut none_bytes = none_rec.encode();
        assert_eq!(BootLeaseRecord::decode(&none_bytes).unwrap(), none_rec);

        // Non-zero byte in boot_id when flag == 0 must fail closed.
        none_bytes[12] = 1;
        assert!(BootLeaseRecord::decode(&none_bytes).is_err());
    }
}
