//! FORMAT 2 `<log>.id` weak-tier power-loss generation mover (`broker.unclean-generation`).

#[cfg(clean_islands)]
#[path = "unclean_boot_generation_mover_island.rs"]
mod unclean_boot_generation_mover_island;
#[cfg(clean_islands)]
pub use unclean_boot_generation_mover_island::{unclean_floor_clamp, unclean_gen_advance};
#[cfg(not(clean_islands))]
#[must_use]
pub const fn unclean_gen_advance(prev_gen: u64, next_gen: u64) -> u64 {
    if prev_gen < next_gen {
        next_gen
    } else {
        prev_gen
    }
}
#[cfg(not(clean_islands))]
#[must_use]
pub const fn unclean_floor_clamp(floor: u64, head: u64) -> u64 {
    if floor < head {
        floor
    } else {
        head
    }
}

contract_fn! {
    #[must_use]
    pub const fn unclean_flag_active(flag: u64) -> bool
    clauses [ensures result == (1 <= flag)]
    {
        1 <= flag
    }
}

#[inline]
#[must_use]
pub const fn unclean_requires_gen_move(weak_tier: u64, left_open: u64, boot_mismatch: u64) -> bool {
    unclean_flag_active(weak_tier)
        && unclean_flag_active(left_open)
        && unclean_flag_active(boot_mismatch)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UncleanBootOutcome {
    pub generation: u64,
    pub durable_floor: u64,
    pub moved_for_power_loss: bool,
}

#[must_use]
pub const fn settle_boot_open(
    prior_generation: u64,
    prior_floor: u64,
    recovered_head: u64,
    served_weak_tier: bool,
    left_open_or_lossy: bool,
    boot_or_volume_untrusted: bool,
) -> UncleanBootOutcome {
    let weak = if served_weak_tier { 1 } else { 0 };
    let open = if left_open_or_lossy { 1 } else { 0 };
    let mismatch = if boot_or_volume_untrusted { 1 } else { 0 };
    let floor = unclean_floor_clamp(prior_floor, recovered_head);
    if unclean_requires_gen_move(weak, open, mismatch) {
        let next = prior_generation.saturating_add(1);
        UncleanBootOutcome {
            generation: unclean_gen_advance(prior_generation, next),
            durable_floor: floor,
            moved_for_power_loss: true,
        }
    } else {
        UncleanBootOutcome {
            generation: prior_generation,
            durable_floor: floor,
            moved_for_power_loss: false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn moves_generation_on_weak_tier_reboot_left_open_and_preserves_strict_or_same_boot() {
        let rebooted = settle_boot_open(4, 120, 100, true, true, true);
        assert_eq!(
            rebooted,
            UncleanBootOutcome {
                generation: 5,
                durable_floor: 100,
                moved_for_power_loss: true,
            }
        );
        let same_boot = settle_boot_open(4, 90, 100, true, true, false);
        assert_eq!(same_boot.generation, 4);
        assert!(!same_boot.moved_for_power_loss);
        let strict = settle_boot_open(4, 100, 100, false, true, true);
        assert_eq!(strict.generation, 4);
    }
}
