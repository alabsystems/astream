//! 1-to-1 Kafka topic-partition to `ShardedBroker` shard router & HWM tracker.

#![allow(
    clippy::manual_map,
    clippy::question_mark,
    clippy::manual_unwrap_or,
    clippy::manual_unwrap_or_default,
    clippy::manual_range_contains,
    clippy::vec_init_then_push,
    clippy::while_let_on_iterator,
    clippy::needless_borrows_for_generic_args
)]

#[cfg(clean_islands)]
#[path = "durable_kafka_shard_mapper_island.rs"]
mod durable_kafka_shard_mapper_island;
#[cfg(clean_islands)]
pub use durable_kafka_shard_mapper_island::{durable_hwm_advance, durable_partition_idx_clamp};
#[cfg(not(clean_islands))]
#[must_use]
pub const fn durable_partition_idx_clamp(part: u64) -> u64 {
    if part < 128 {
        part
    } else {
        128
    }
}
#[cfg(not(clean_islands))]
#[must_use]
pub const fn durable_hwm_advance(prev_hwm: u64, next_hwm: u64) -> u64 {
    if prev_hwm < next_hwm {
        next_hwm
    } else {
        prev_hwm
    }
}

contract_fn! {
    #[must_use]
    pub const fn durable_partition_in_range(part: u64, num_partitions: u64) -> bool
    clauses [ensures result == ((part < num_partitions))]
    {
        part < num_partitions
    }
}

pub const MAX_DURABLE_PARTITIONS: usize = 128;
pub const KAFKA_ERR_UNKNOWN_TOPIC_OR_PARTITION: i16 = 3;

#[derive(Debug, Clone)]
pub struct DurableKafkaShardMapper {
    num_partitions: usize,
    hwms: [u64; MAX_DURABLE_PARTITIONS],
}

impl DurableKafkaShardMapper {
    #[must_use]
    pub const fn new(num_partitions: usize) -> Option<Self> {
        if num_partitions == 0 || num_partitions > MAX_DURABLE_PARTITIONS {
            return None;
        }
        Some(Self {
            num_partitions,
            hwms: [0; MAX_DURABLE_PARTITIONS],
        })
    }

    #[must_use]
    pub const fn num_partitions(&self) -> usize {
        self.num_partitions
    }

    #[must_use]
    #[allow(clippy::manual_map)]
    pub fn hwm(&self, shard: usize) -> Option<u64> {
        if shard < self.num_partitions {
            match self.hwms.get(shard) {
                Some(&v) => Some(v),
                None => None,
            }
        } else {
            None
        }
    }

    pub const fn resolve_shard(&self, partition: i32) -> Result<usize, i16> {
        if partition < 0 {
            return Err(KAFKA_ERR_UNKNOWN_TOPIC_OR_PARTITION);
        }
        let p = partition as u64;
        if p >= MAX_DURABLE_PARTITIONS as u64
            || !durable_partition_in_range(p, self.num_partitions as u64)
        {
            return Err(KAFKA_ERR_UNKNOWN_TOPIC_OR_PARTITION);
        }
        let clamped = durable_partition_idx_clamp(p) as usize;
        if clamped >= MAX_DURABLE_PARTITIONS {
            return Err(KAFKA_ERR_UNKNOWN_TOPIC_OR_PARTITION);
        }
        Ok(clamped)
    }

    #[allow(clippy::question_mark)]
    pub fn record_append(&mut self, partition: i32, next_offset: u64) -> Result<u64, i16> {
        let shard = match self.resolve_shard(partition) {
            Ok(s) => s,
            Err(e) => return Err(e),
        };
        let Some(slot) = self.hwms.get_mut(shard) else {
            return Err(KAFKA_ERR_UNKNOWN_TOPIC_OR_PARTITION);
        };
        let hwm = durable_hwm_advance(*slot, next_offset);
        *slot = hwm;
        Ok(hwm)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn maps_partitions_bijectively_and_rejects_negative_or_out_of_bounds() {
        let mut m = DurableKafkaShardMapper::new(4).unwrap();
        assert_eq!(m.num_partitions(), 4);
        assert_eq!(
            m.resolve_shard(-1),
            Err(KAFKA_ERR_UNKNOWN_TOPIC_OR_PARTITION)
        );
        assert_eq!(
            m.resolve_shard(4),
            Err(KAFKA_ERR_UNKNOWN_TOPIC_OR_PARTITION)
        );
        assert_eq!(m.record_append(2, 15), Ok(15));
        assert_eq!(m.record_append(2, 10), Ok(15));
        assert_eq!(m.hwm(2), Some(15));
    }
}
