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

use crate::hash::{fnv1a_64, fnv1a_64_update, FNV1A_64_INIT};

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "partition_island.rs"]
mod partition_island;
#[cfg(not(clean_islands))]
pub use crate::twins::partition_modulus_clamp;
#[cfg(clean_islands)]
pub use partition_island::partition_modulus_clamp;

contract_fn! {
    /// Whether assigned `partition` is strictly below the nonzero `modulus` (`partition < modulus`).
    ///
    /// Verified against `Astream.Wire.TlaPartitionRouter.partition_in_bounds_isl` by
    /// `clean-kernel-defeq`.
    pub const fn partition_in_bounds(partition: u64, modulus: u64) -> bool
    clauses [ensures result == (partition < modulus)]
    {
        partition < modulus
    }
}

/// Width of the sticky time bucket for unkeyed durable messages, in ms.
/// A tunable knob; coarse enough to batch, fine enough to rebalance.
pub const TIME_BUCKET_MS: u64 = 2000;

/// Map a millisecond timestamp to its sticky bucket index.
#[must_use]
pub const fn time_bucket(timestamp_ms: u64) -> u64 {
    timestamp_ms / TIME_BUCKET_MS
}

const fn slice_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut ar = a;
    let mut br = b;
    while let &[x, ref ta @ ..] = ar {
        let &[y, ref tb @ ..] = br else {
            return false;
        };
        if x != y {
            return false;
        }
        ar = ta;
        br = tb;
    }
    true
}

/// What determines a message's partition. Borrowed, so this stays allocation-
/// free for all three routing variants.
#[derive(Debug, Clone, Copy, Eq)]
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

impl PartialEq for PartitionKey<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Keyed(a), Self::Keyed(b)) => slice_eq(a, b),
            (
                Self::UnkeyedDurable {
                    topic: t1,
                    origin: o1,
                    time_bucket: b1,
                },
                Self::UnkeyedDurable {
                    topic: t2,
                    origin: o2,
                    time_bucket: b2,
                },
            ) => {
                slice_eq(t1.as_bytes(), t2.as_bytes())
                    && slice_eq(o1.as_bytes(), o2.as_bytes())
                    && *b1 == *b2
            }
            (Self::UnkeyedEphemeral { msg_id: a }, Self::UnkeyedEphemeral { msg_id: b }) => {
                *a == *b
            }
            (Self::Keyed(_), _)
            | (Self::UnkeyedDurable { .. }, _)
            | (Self::UnkeyedEphemeral { .. }, _) => false,
        }
    }
}

/// Assign a partition in `0..num_partitions.max(1)`. Deterministic, allocation-free,
/// and always in bounds (the `.max(1)` guard — matching [`partition_modulus_clamp`]
/// with `floor = 1` — means `num_partitions == 0` maps to 1).
#[must_use]
pub const fn assign_partition(key: PartitionKey<'_>, num_partitions: u32) -> u32 {
    let clamped = if num_partitions > 1 {
        num_partitions
    } else {
        1
    };
    let n = clamped as u64;
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
            // Streamed directly through FNV-1a with zero heap allocation.
            let h = fnv1a_64_update(FNV1A_64_INIT, &(topic.len() as u64).to_le_bytes());
            let h = fnv1a_64_update(h, topic.as_bytes());
            let h = fnv1a_64_update(h, &(origin.len() as u64).to_le_bytes());
            let h = fnv1a_64_update(h, origin.as_bytes());
            fnv1a_64_update(h, &time_bucket.to_le_bytes())
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
            let modulus = partition_modulus_clamp(n as u64, 1);
            assert_eq!(modulus, n.max(1) as u64);
            for key in keys {
                let p = assign_partition(key, n);
                assert!(
                    partition_in_bounds(p as u64, modulus),
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
