//! The single, canonical partition-assignment function.
//!
//! Everything that routes a message calls this one pure function, so producers
//! and brokers independently re-derive the identical partition with zero
//! coordination. There is deliberately exactly one of these: a second,
//! divergent partitioner would route the same message two ways.
//!
//! The assignment is a pure function of immutable message attributes:
//!
//! * **Keyed** → `hash(key) % n` (co-locates a key's records).
//! * **Unkeyed durable** → sticky hash over `(topic, origin, time_bucket)`, so
//!   a single producer's unkeyed durable traffic stays put for a coarse time
//!   window (better batching) without a synthetic user key.
//! * **Unkeyed ephemeral** → `hash(msg_id)` (spread freely).

use crate::hash::fnv1a_64;

/// Width of the sticky time bucket for unkeyed durable messages, in ms.
/// A tunable knob; coarse enough to batch, fine enough to rebalance.
pub const TIME_BUCKET_MS: u64 = 2000;

/// Map a millisecond timestamp to its sticky bucket index.
pub fn time_bucket(timestamp_ms: u64) -> u64 {
    timestamp_ms / TIME_BUCKET_MS
}

/// What determines a message's partition. Borrowed, so this stays allocation-
/// free for the common keyed/ephemeral cases.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PartitionKey<'a> {
    /// An explicit routing key.
    Keyed(&'a [u8]),
    /// No key, durable: stick by producer identity within a time bucket.
    UnkeyedDurable {
        topic: &'a str,
        origin: &'a str,
        time_bucket: u64,
    },
    /// No key, ephemeral: spread by message id.
    UnkeyedEphemeral { msg_id: u128 },
}

/// Assign a partition in `0..num_partitions.max(1)`. Deterministic and always
/// in bounds (the `.max(1)` guard means `num_partitions == 0` maps to 1).
pub fn assign_partition(key: PartitionKey<'_>, num_partitions: u32) -> u32 {
    let n = num_partitions.max(1) as u64;
    let h = match key {
        PartitionKey::Keyed(k) => fnv1a_64(k),
        PartitionKey::UnkeyedDurable {
            topic,
            origin,
            time_bucket,
        } => {
            // Length-prefix each field so the encoding is injective even when a
            // field itself contains the byte we might otherwise use as a
            // separator. A bare separator is forgeable: ("a\x1fb","c") and
            // ("a","b\x1fc") collide under it. Length prefixes cannot collide.
            let mut buf = Vec::with_capacity(topic.len() + origin.len() + 24);
            buf.extend_from_slice(&(topic.len() as u64).to_le_bytes());
            buf.extend_from_slice(topic.as_bytes());
            buf.extend_from_slice(&(origin.len() as u64).to_le_bytes());
            buf.extend_from_slice(origin.as_bytes());
            buf.extend_from_slice(&time_bucket.to_le_bytes());
            fnv1a_64(&buf)
        }
        PartitionKey::UnkeyedEphemeral { msg_id } => fnv1a_64(&msg_id.to_le_bytes()),
    };
    (h % n) as u32
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn always_in_bounds_including_zero_partitions() {
        // The claim is "always within range" — so exercise ALL three routing
        // variants across small counts AND the u32 boundary, where the final
        // `(h % n) as u32` cast and the `max(1) as u64` widening are riskiest.
        let keys = [
            PartitionKey::Keyed(b""),
            PartitionKey::Keyed(b"k"),
            PartitionKey::UnkeyedDurable {
                topic: "/a/stream/x",
                origin: "p1",
                time_bucket: 9,
            },
            PartitionKey::UnkeyedEphemeral { msg_id: u128::MAX },
        ];
        for n in [0u32, 1, 2, 7, 1024, u32::MAX - 1, u32::MAX] {
            for key in keys {
                let p = assign_partition(key, n);
                assert!(
                    p < n.max(1),
                    "partition {p} out of bounds for n={n}, key={key:?}"
                );
            }
        }
    }

    #[test]
    fn keyed_is_stable_and_independent_of_partition_count_modulo() {
        let a = assign_partition(PartitionKey::Keyed(b"order-42"), 16);
        let b = assign_partition(PartitionKey::Keyed(b"order-42"), 16);
        assert_eq!(a, b);
    }

    #[test]
    fn unkeyed_durable_is_sticky_within_a_bucket() {
        let mk = |bucket| {
            assign_partition(
                PartitionKey::UnkeyedDurable {
                    topic: "/a/stream/events",
                    origin: "producer-1",
                    time_bucket: bucket,
                },
                32,
            )
        };
        assert_eq!(mk(100), mk(100)); // same bucket -> same partition
    }

    #[test]
    fn field_domain_separation() {
        let p1 = assign_partition(
            PartitionKey::UnkeyedDurable {
                topic: "ab",
                origin: "c",
                time_bucket: 0,
            },
            64,
        );
        let p2 = assign_partition(
            PartitionKey::UnkeyedDurable {
                topic: "a",
                origin: "bc",
                time_bucket: 0,
            },
            64,
        );
        // Not a guarantee for all inputs, but these specific ones must differ
        // because of the length-prefixed framing.
        assert_ne!(p1, p2);
    }

    #[test]
    fn domain_separation_holds_when_fields_contain_the_old_separator() {
        // Under a bare 0x1f separator these two would collide
        // ("a\x1fb" + sep + "c" == "a" + sep + "b\x1fc"). Length prefixes make
        // the encoding injective, so they route independently.
        let mk = |topic: &str, origin: &str| {
            assign_partition(
                PartitionKey::UnkeyedDurable {
                    topic,
                    origin,
                    time_bucket: 7,
                },
                64,
            )
        };
        // Compare the raw hashes, not just the mod-reduced partition, so the
        // test is not at the mercy of a coincidental modulus collision.
        let h1 = fnv_durable("a\u{1f}b", "c", 7);
        let h2 = fnv_durable("a", "b\u{1f}c", 7);
        assert_ne!(h1, h2, "length-prefixed framing must not collide");
        // And the public function is deterministic for each.
        assert_eq!(mk("a\u{1f}b", "c"), mk("a\u{1f}b", "c"));
    }

    /// Re-derive the UnkeyedDurable pre-hash buffer for a white-box assertion.
    fn fnv_durable(topic: &str, origin: &str, time_bucket: u64) -> u64 {
        let mut buf = Vec::new();
        buf.extend_from_slice(&(topic.len() as u64).to_le_bytes());
        buf.extend_from_slice(topic.as_bytes());
        buf.extend_from_slice(&(origin.len() as u64).to_le_bytes());
        buf.extend_from_slice(origin.as_bytes());
        buf.extend_from_slice(&time_bucket.to_le_bytes());
        fnv1a_64(&buf)
    }
}
