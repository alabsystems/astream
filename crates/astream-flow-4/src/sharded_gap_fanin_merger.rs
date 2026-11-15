//! Per-shard `ShardedEvent::Gap` ordering tracker for sharded subscription fan-in.

#[cfg(clean_islands)]
#[path = "sharded_gap_fanin_merger_island.rs"]
mod sharded_gap_fanin_merger_island;
#[cfg(clean_islands)]
pub use sharded_gap_fanin_merger_island::{shard_gap_floor_advance, shard_index_clamp};

#[cfg(not(clean_islands))]
#[must_use]
pub const fn shard_gap_floor_advance(prev_floor: u64, gap_to: u64) -> u64 {
    if prev_floor < gap_to {
        gap_to
    } else {
        prev_floor
    }
}

#[cfg(not(clean_islands))]
#[must_use]
pub const fn shard_index_clamp(shard_idx: u64) -> u64 {
    if shard_idx < 64 {
        shard_idx
    } else {
        64
    }
}

contract_fn! {
    #[must_use]
    pub const fn shard_delivery_ordered_after_gap(told_floor: u64, rec_offset: u64) -> bool
    clauses [ensures result == (told_floor <= rec_offset)]
    {
        told_floor <= rec_offset
    }
}

pub const MAX_FANIN_SHARDS: usize = 64;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShardFaninError {
    InvalidShard {
        shard: usize,
        count: usize,
    },
    DeliveryBelowToldGap {
        shard: usize,
        rec_offset: u64,
        told_floor: u64,
    },
}

#[derive(Debug, Clone)]
pub struct ShardedGapFaninMerger {
    shard_count: usize,
    told_floors: [u64; MAX_FANIN_SHARDS],
    next_cursors: [u64; MAX_FANIN_SHARDS],
}

impl ShardedGapFaninMerger {
    #[must_use]
    pub const fn new(shard_count: usize) -> Option<Self> {
        if shard_count == 0 || shard_count > MAX_FANIN_SHARDS {
            return None;
        }
        Some(Self {
            shard_count,
            told_floors: [0; MAX_FANIN_SHARDS],
            next_cursors: [0; MAX_FANIN_SHARDS],
        })
    }

    #[must_use]
    pub const fn shard_count(&self) -> usize {
        self.shard_count
    }

    pub fn observe_gap(
        &mut self,
        shard: usize,
        from: u64,
        to: u64,
    ) -> Result<u64, ShardFaninError> {
        if shard >= self.shard_count || shard >= MAX_FANIN_SHARDS {
            return Err(ShardFaninError::InvalidShard {
                shard,
                count: self.shard_count,
            });
        }
        let idx = shard_index_clamp(shard as u64) as usize;
        let _ = from;
        let prev = match self.told_floors.get(idx) {
            Some(&v) => v,
            None => 0,
        };
        let floor = shard_gap_floor_advance(prev, to);
        if let Some(slot) = self.told_floors.get_mut(idx) {
            *slot = floor;
        }
        if let Some(cur) = self.next_cursors.get_mut(idx) {
            if *cur < floor {
                *cur = floor;
            }
        }
        Ok(floor)
    }

    pub fn admit_delivery(
        &mut self,
        shard: usize,
        rec_offset: u64,
    ) -> Result<u64, ShardFaninError> {
        if shard >= self.shard_count || shard >= MAX_FANIN_SHARDS {
            return Err(ShardFaninError::InvalidShard {
                shard,
                count: self.shard_count,
            });
        }
        let idx = shard_index_clamp(shard as u64) as usize;
        let floor = match self.told_floors.get(idx) {
            Some(&v) => v,
            None => 0,
        };
        if !shard_delivery_ordered_after_gap(floor, rec_offset) {
            return Err(ShardFaninError::DeliveryBelowToldGap {
                shard,
                rec_offset,
                told_floor: floor,
            });
        }
        let next = rec_offset.saturating_add(1);
        if let Some(cur) = self.next_cursors.get_mut(idx) {
            if *cur < next {
                *cur = next;
            }
            Ok(*cur)
        } else {
            Ok(next)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enforces_per_shard_gap_floor_independently_across_shards() {
        let mut m = ShardedGapFaninMerger::new(4).unwrap();
        assert_eq!(m.shard_count(), 4);
        assert_eq!(m.observe_gap(1, 0, 50), Ok(50));
        assert_eq!(m.admit_delivery(0, 0), Ok(1));
        assert_eq!(
            m.admit_delivery(1, 49),
            Err(ShardFaninError::DeliveryBelowToldGap {
                shard: 1,
                rec_offset: 49,
                told_floor: 50,
            })
        );
        assert_eq!(m.admit_delivery(1, 50), Ok(51));
    }
}
