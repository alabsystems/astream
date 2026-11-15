// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The laws of `astream_wire::summary`: merging is an exact commutative monoid (and not
//! idempotent), quantiles keep their stated error bound at every rank, fine windows roll
//! up to coarse ones exactly, a `Rollup` counts each origin's newest row once whatever the
//! delivery, the encodings round-trip and refuse what is not theirs, and a day of real
//! agent token counts reads back within the bound in a few hundred bytes.

use astream_wire::summary::{
    bucket_bounds, bucket_index, Counter, DecodeError, Gauge, MetricName, NameError, Offered,
    Origin, Quantile, Rollup, Summary, SummaryId, Window, WindowLen, BUCKET_COUNT, KIND_COUNTER,
    KIND_GAUGE, KIND_ID, KIND_SUMMARY, MAX_NAME_LEN, MAX_SUMMARY_LEN, QUANTILE_ERROR_DIVISOR,
    SUMMARY_VERSION,
};
use proptest::prelude::*;
use std::collections::{BTreeMap, BTreeSet};

const MINUTE: u64 = 60_000;
const HOUR: u64 = 60 * MINUTE;
const DAY: u64 = 24 * HOUR;
/// Monday 2026-11-02 00:00 UTC.
const MONDAY_2026_11_02_MS: u64 = 1_793_577_600_000;

// ---------------------------------------------------------------------------
// Strategies and helpers
// ---------------------------------------------------------------------------

/// Values that hit unit buckets, realistic magnitudes, the whole range, and both sides of
/// every power-of-two edge.
fn value() -> impl Strategy<Value = u64> {
    prop_oneof![
        0u64..64,
        64u64..2_000_000,
        any::<u64>(),
        (0u32..64).prop_map(|bit| 1u64 << bit),
        (1u32..=64).prop_map(|bit| u64::MAX >> (64 - bit)),
    ]
}

fn values() -> impl Strategy<Value = Vec<u64>> {
    prop::collection::vec(value(), 0..160)
}

/// Summaries of plain multisets, and of weighted ones heavy enough to saturate counts.
fn summary() -> impl Strategy<Value = Summary> {
    let weight = prop_oneof![1u64..1_000, (u64::MAX / 4)..=u64::MAX];
    prop_oneof![
        3 => values().prop_map(Summary::of),
        1 => prop::collection::vec((value(), weight), 0..12).prop_map(|weighted| {
            let mut summary = Summary::new();
            for (value, n) in weighted {
                summary.record_n(value, n);
            }
            summary
        }),
    ]
}

fn window_len() -> impl Strategy<Value = WindowLen> {
    prop::sample::select(WindowLen::ALL.to_vec())
}

/// A finer-or-equal and a coarser-or-equal length.
fn fine_and_coarse() -> impl Strategy<Value = (WindowLen, WindowLen)> {
    (0usize..4, 0usize..4).prop_map(|(a, b)| (WindowLen::ALL[a.min(b)], WindowLen::ALL[a.max(b)]))
}

/// Instants after `MONDAY_2026_11_02_MS`, spread over ten days or clustered in a few hours.
fn offset_ms() -> impl Strategy<Value = u64> {
    prop_oneof![0u64..10 * DAY, 0u64..3 * HOUR, 0u64..5 * MINUTE]
}

fn origin(n: usize) -> Origin {
    Origin::new(&format!("n-{n:016x}")).expect("a node id is a valid origin")
}

fn metric(name: &str) -> MetricName {
    MetricName::new(name).expect("a valid metric name")
}

fn minute_at(offset: u64) -> Window {
    Window::containing(MONDAY_2026_11_02_MS + offset, WindowLen::Minute).expect("in range")
}

fn put_varint(out: &mut Vec<u8>, mut value: u128) {
    loop {
        let group = (value & 0x7f) as u8;
        value >>= 7;
        if value == 0 {
            out.push(group);
            return;
        }
        out.push(group | 0x80);
    }
}

/// The summary format written from its spec, independently of `Summary::encode`.
fn encode_raw(buckets: &[(u16, u64)], min: u64, max: u64, sum: u128) -> Vec<u8> {
    let mut out = vec![KIND_SUMMARY, SUMMARY_VERSION];
    put_varint(&mut out, buckets.len() as u128);
    let mut next = 0u64;
    for &(index, count) in buckets {
        put_varint(&mut out, u128::from(u64::from(index) - next));
        put_varint(&mut out, u128::from(count));
        next = u64::from(index) + 1;
    }
    if !buckets.is_empty() {
        put_varint(&mut out, u128::from(min));
        put_varint(&mut out, u128::from(max));
        put_varint(&mut out, sum);
    }
    out
}

/// A splitmix64 step: the test's own deterministic shuffle source.
fn mix(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

fn shuffle<T>(items: &mut [T], seed: u64) {
    let mut state = seed;
    for at in (1..items.len()).rev() {
        let pick = (mix(&mut state) % (at as u64 + 1)) as usize;
        items.swap(at, pick);
    }
}

// ---------------------------------------------------------------------------
// The bucket layout
// ---------------------------------------------------------------------------

#[test]
fn the_buckets_tile_every_u64_in_order_and_are_at_most_one_thirty_second_wide() {
    let mut expected_low = 0u64;
    for index in 0..BUCKET_COUNT {
        let (low, high) = bucket_bounds(index).expect("an index in the layout has bounds");
        assert_eq!(
            low, expected_low,
            "bucket {index} starts where the one before ended"
        );
        assert!(low <= high, "bucket {index} is not empty");
        assert_eq!(
            bucket_index(low),
            index,
            "bucket {index}'s low end maps back to it"
        );
        assert_eq!(
            bucket_index(high),
            index,
            "bucket {index}'s high end maps back to it"
        );
        let width = high - low + 1;
        if low < 64 {
            assert_eq!(width, 1, "bucket {index} below 64 holds one value");
        } else {
            assert!(
                width * 32 <= low,
                "bucket {index} is at most 1/32 of its low end wide"
            );
        }
        expected_low = high.wrapping_add(1);
    }
    assert_eq!(expected_low, 0, "the last bucket ends at u64::MAX");
    assert_eq!(bucket_bounds(BUCKET_COUNT), None);
    assert_eq!(bucket_index(u64::MAX), BUCKET_COUNT - 1);
}

proptest! {
    #[test]
    fn every_value_lies_in_its_own_bucket(v in value()) {
        let (low, high) = bucket_bounds(bucket_index(v)).expect("every value has a bucket");
        prop_assert!(low <= v && v <= high, "{} outside [{}, {}]", v, low, high);
    }
}

// ---------------------------------------------------------------------------
// Merge laws
// ---------------------------------------------------------------------------

proptest! {
    #[test]
    fn count_sum_min_and_max_are_exact(xs in values()) {
        let summary = Summary::of(xs.iter().copied());
        prop_assert_eq!(summary.count(), xs.len() as u64);
        prop_assert_eq!(summary.sum(), xs.iter().map(|&v| u128::from(v)).sum::<u128>());
        prop_assert_eq!(summary.min(), xs.iter().copied().min());
        prop_assert_eq!(summary.max(), xs.iter().copied().max());
        prop_assert_eq!(summary.is_empty(), xs.is_empty());
        prop_assert_eq!(summary.buckets().map(|(_, n)| n).sum::<u64>(), summary.count());
    }

    #[test]
    fn the_empty_summary_is_the_identity_of_merge(a in summary()) {
        prop_assert_eq!(a.clone().merged(&Summary::new()), a.clone());
        prop_assert_eq!(Summary::new().merged(&a), a);
    }

    #[test]
    fn merge_is_commutative(a in summary(), b in summary()) {
        prop_assert_eq!(a.clone().merged(&b), b.merged(&a));
    }

    #[test]
    fn merge_is_associative(a in summary(), b in summary(), c in summary()) {
        prop_assert_eq!(a.clone().merged(&b).merged(&c), a.merged(&b.clone().merged(&c)));
    }

    #[test]
    fn the_summary_of_two_runs_is_the_merge_of_their_summaries(xs in values(), ys in values()) {
        let both = xs.iter().chain(&ys).copied();
        prop_assert_eq!(
            Summary::of(xs.iter().copied()).merged(&Summary::of(ys.iter().copied())),
            Summary::of(both)
        );
    }

    #[test]
    fn recording_n_at_once_equals_n_records(v in value(), n in 0u64..300, base in values()) {
        let mut at_once = Summary::of(base.iter().copied());
        at_once.record_n(v, n);
        let mut one_by_one = Summary::of(base);
        for _ in 0..n {
            one_by_one.record(v);
        }
        prop_assert_eq!(at_once, one_by_one);
    }

    #[test]
    fn merge_is_not_idempotent_a_summary_merged_with_itself_counts_twice(
        xs in prop::collection::vec(value(), 1..80),
    ) {
        let summary = Summary::of(xs.iter().copied());
        let twice = summary.clone().merged(&summary);
        prop_assert_ne!(&twice, &summary);
        prop_assert_eq!(twice.count(), 2 * summary.count());
        prop_assert_eq!(twice, Summary::of(xs.iter().chain(&xs).copied()));
    }
}

// ---------------------------------------------------------------------------
// Quantiles
// ---------------------------------------------------------------------------

proptest! {
    #[test]
    fn every_rank_reads_within_one_sixty_fourth_of_its_exact_value(xs in values(), ys in values()) {
        // Read through a merge: merged summaries are what a reader holds.
        let summary = Summary::of(xs.iter().copied()).merged(&Summary::of(ys.iter().copied()));
        let mut sorted: Vec<u64> = xs.into_iter().chain(ys).collect();
        sorted.sort_unstable();
        let n = sorted.len() as u64;
        prop_assert_eq!(summary.value_at_rank(0), None);
        prop_assert_eq!(summary.value_at_rank(n + 1), None);
        let mut previous = 0u64;
        for (at, &exact) in sorted.iter().enumerate() {
            let rank = at as u64 + 1;
            let read = summary.value_at_rank(rank).expect("a rank within the count reads");
            prop_assert!(
                summary.min() <= Some(read) && Some(read) <= summary.max(),
                "rank {} read {} outside [min, max]", rank, read
            );
            prop_assert!(read >= previous, "rank {} read {} below {}", rank, read, previous);
            previous = read;
            prop_assert!(
                u128::from(read.abs_diff(exact)) * u128::from(QUANTILE_ERROR_DIVISOR)
                    <= u128::from(exact),
                "rank {} read {} for {}", rank, read, exact
            );
            if exact < 64 || rank == 1 || rank == n {
                prop_assert_eq!(read, exact, "rank {} is exact", rank);
            }
        }
    }

    #[test]
    fn a_quantile_reads_its_nearest_rank(
        xs in prop::collection::vec(value(), 1..120),
        ppm in 0u32..=1_000_000,
    ) {
        let q = Quantile::per_million(ppm).expect("at most one million");
        prop_assert_eq!(q.as_per_million(), ppm);
        let summary = Summary::of(xs.iter().copied());
        let n = xs.len() as u64;
        let nearest = ((u128::from(ppm) * u128::from(n)).div_ceil(1_000_000) as u64).max(1);
        prop_assert_eq!(q.rank(n), nearest);
        prop_assert_eq!(summary.quantile(q), summary.value_at_rank(nearest));
    }
}

#[test]
fn the_extreme_quantiles_are_the_exact_extremes_and_an_empty_summary_has_none() {
    // Both in the bucket [992, 1007], whose midpoint 999 neither extreme is.
    let summary = Summary::of([995, 1007]);
    assert_eq!(bucket_bounds(bucket_index(995)), Some((992, 1007)));
    assert_eq!(summary.quantile(Quantile::MIN), Some(995));
    assert_eq!(summary.quantile(Quantile::MAX), Some(1007));
    // 1050 lies in [1024, 1055], whose midpoint 1039 is below the minimum: the clamp answers.
    let repeated = Summary::of([1050, 1050, 1050]);
    let reads: Vec<_> = (1..=3).map(|rank| repeated.value_at_rank(rank)).collect();
    assert_eq!(reads, [Some(1050); 3]);
    assert_eq!(Summary::new().quantile(Quantile::P50), None);
    assert_eq!(Summary::new().quantile(Quantile::MAX), None);
    assert_eq!(Summary::new().min(), None);
    assert_eq!(Quantile::P99.rank(0), 0);
    assert_eq!(Quantile::per_million(1_000_000), Some(Quantile::MAX));
    assert_eq!(Quantile::per_million(0), Some(Quantile::MIN));
    assert_eq!(Quantile::per_million(1_000_001), None);
}

proptest! {
    #[test]
    fn the_extremes_are_exact_in_wide_buckets(xs in prop::collection::vec(64u64.., 2..40)) {
        let summary = Summary::of(xs.iter().copied());
        prop_assert_eq!(summary.quantile(Quantile::MIN), xs.iter().min().copied());
        prop_assert_eq!(summary.quantile(Quantile::MAX), xs.iter().max().copied());
    }
}

/// `u64::MAX` zeros and one 1,000,000: the count saturates, the last rank is a zero, and
/// the maximum is still the maximum.
#[test]
fn at_a_saturated_count_every_rank_keeps_the_bound_and_the_maximum_stays_exact() {
    let mut a = Summary::new();
    a.record_n(0, 1 << 63);
    let mut b = Summary::new();
    b.record_n(0, (1 << 63) - 1);
    b.record(1_000_000);
    let merged = a.merged(&b);
    assert_eq!(merged.count(), u64::MAX);
    assert_eq!(
        merged.value_at_rank(u64::MAX),
        Some(0),
        "the true value at that rank"
    );
    assert_eq!(merged.quantile(Quantile::MAX), Some(1_000_000));
    assert_eq!(merged.quantile(Quantile::MIN), Some(0));
    assert_eq!(Summary::decode(&merged.encode()), Ok(merged.clone()));
    // Saturated bucket counts stay saturated through a merge, and still decode.
    let mut heavy = Summary::new();
    heavy.record_n(5, u64::MAX);
    heavy.record(5);
    assert_eq!(heavy.buckets().collect::<Vec<_>>(), [(5, u64::MAX)]);
    assert_eq!(heavy.sum(), 5 * (u128::from(u64::MAX) + 1));
    assert_eq!(Summary::decode(&heavy.encode()), Ok(heavy.clone()));
    let doubled = heavy.clone().merged(&heavy);
    assert_eq!(doubled.buckets().collect::<Vec<_>>(), [(5, u64::MAX)]);
    assert_eq!(doubled.count(), u64::MAX);
    assert_eq!(Summary::decode(&doubled.encode()), Ok(doubled));
}

// ---------------------------------------------------------------------------
// The summary encoding
// ---------------------------------------------------------------------------

proptest! {
    #[test]
    fn a_summary_round_trips_through_its_canonical_encoding(a in summary(), b in summary()) {
        for summary in [a.clone(), a.merged(&b)] {
            let bytes = summary.encode();
            prop_assert_eq!(bytes.len(), summary.encoded_len());
            prop_assert!(bytes.len() <= MAX_SUMMARY_LEN);
            let buckets: Vec<(u16, u64)> = summary.buckets().collect();
            let raw = encode_raw(
                &buckets,
                summary.min().unwrap_or(0),
                summary.max().unwrap_or(0),
                summary.sum(),
            );
            prop_assert_eq!(&raw, &bytes, "the encoder writes the documented format");
            let mut appended = vec![0xAA];
            summary.encode_into(&mut appended);
            prop_assert_eq!(&appended[1..], &bytes[..]);
            prop_assert_eq!(Summary::decode(&bytes), Ok(summary));
        }
    }

    #[test]
    fn every_proper_prefix_of_an_encoding_is_refused_and_so_is_a_longer_one(s in summary()) {
        let bytes = s.encode();
        for cut in 0..bytes.len() {
            prop_assert!(Summary::decode(&bytes[..cut]).is_err(), "prefix of {} bytes", cut);
        }
        let mut longer = bytes;
        longer.push(0);
        prop_assert_eq!(Summary::decode(&longer), Err(DecodeError::TrailingBytes));
    }

    #[test]
    fn a_damaged_encoding_is_refused_or_is_the_canonical_encoding_of_what_it_decodes_to(
        s in summary(),
        at in any::<prop::sample::Index>(),
        byte in any::<u8>(),
    ) {
        let mut bytes = s.encode();
        let at = at.index(bytes.len());
        bytes[at] = byte;
        if let Ok(decoded) = Summary::decode(&bytes) {
            prop_assert_eq!(decoded.encode(), bytes);
        }
    }

    #[test]
    fn arbitrary_bytes_never_panic_and_decode_only_as_their_own_encoding(
        tail in prop::collection::vec(any::<u8>(), 0..48),
    ) {
        for kind in [KIND_SUMMARY, KIND_COUNTER, KIND_GAUGE, KIND_ID] {
            let mut bytes = vec![kind, 1];
            bytes.extend_from_slice(&tail);
            if let Ok(summary) = Summary::decode(&bytes) {
                prop_assert_eq!(summary.encode(), bytes.clone());
            }
            if let Ok(counter) = Counter::decode(&bytes) {
                prop_assert_eq!(counter.encode(), bytes.clone());
            }
            if let Ok(gauge) = Gauge::decode(&bytes) {
                prop_assert_eq!(gauge.encode(), bytes.clone());
            }
            if let Ok(id) = SummaryId::decode(&bytes) {
                prop_assert_eq!(id.encode(), bytes.clone());
            }
        }
    }
}

/// The sums some multiset reaches, by its buckets, minimum and maximum.
type Reachable = BTreeMap<(Vec<(u16, u64)>, u64, u64), BTreeSet<u128>>;

/// Every multiset of one to four values drawn from unit, width-2 and width-4 buckets (so a
/// first, middle and last bucket each hold two or more), and every minimum and maximum in
/// and just outside those buckets with every sum near them: the decoder accepts a
/// candidate exactly when some multiset has that summary.
#[test]
fn decoding_accepts_exactly_the_summaries_some_multiset_has() {
    let domain: Vec<u64> = (60..=71).chain(124..=135).collect();
    let mut reachable: Reachable = BTreeMap::new();
    let mut record = |values: &[u64]| {
        let summary = Summary::of(values.iter().copied());
        let key = (
            summary.buckets().collect::<Vec<_>>(),
            summary.min().expect("nonempty"),
            summary.max().expect("nonempty"),
        );
        reachable.entry(key).or_default().insert(summary.sum());
    };
    for (i, &a) in domain.iter().enumerate() {
        record(&[a]);
        for (j, &b) in domain.iter().enumerate().skip(i) {
            record(&[a, b]);
            for (k, &c) in domain.iter().enumerate().skip(j) {
                record(&[a, b, c]);
                for &d in domain.iter().skip(k) {
                    record(&[a, b, c, d]);
                }
            }
        }
    }
    let mut lists: BTreeMap<Vec<(u16, u64)>, (u128, u128)> = BTreeMap::new();
    for ((buckets, _, _), sums) in &reachable {
        let (&least, &most) = (sums.first().expect("a sum"), sums.last().expect("a sum"));
        let span = lists.entry(buckets.clone()).or_insert((least, most));
        span.0 = span.0.min(least);
        span.1 = span.1.max(most);
    }
    let mut accepted = 0usize;
    let mut refused = 0usize;
    for (buckets, &(least, most)) in &lists {
        let first = bucket_bounds(buckets[0].0).expect("in the layout");
        let last = bucket_bounds(buckets[buckets.len() - 1].0).expect("in the layout");
        for min in first.0 - 2..=first.1 + 2 {
            for max in last.0 - 2..=last.1 + 2 {
                let sums = reachable.get(&(buckets.clone(), min, max));
                for sum in least.saturating_sub(2)..=most + 2 {
                    let bytes = encode_raw(buckets, min, max, sum);
                    let expect = sums.is_some_and(|sums| sums.contains(&sum));
                    let got = Summary::decode(&bytes);
                    assert_eq!(
                        got.is_ok(),
                        expect,
                        "buckets {buckets:?} min {min} max {max} sum {sum}: {got:?}"
                    );
                    if expect {
                        accepted += 1;
                    } else {
                        refused += 1;
                    }
                }
            }
        }
    }
    assert!(
        accepted > 1_000 && refused > 1_000,
        "{accepted} accepted, {refused} refused"
    );
}

/// Values packed into a few buckets, so one bucket can hold many values.
fn clustered() -> impl Strategy<Value = Vec<u64>> {
    let group = (
        0u16..BUCKET_COUNT,
        prop::collection::vec(any::<u64>(), 1..12),
    );
    prop::collection::vec(group, 1..5).prop_map(|groups| {
        let mut values = Vec::new();
        for (index, raw) in groups {
            let (low, high) = bucket_bounds(index).expect("in the layout");
            values.extend(raw.into_iter().map(|r| low + r % (high - low + 1)));
        }
        values
    })
}

proptest! {
    /// Moving every value but the two extremes to the low (high) end of what its bucket and
    /// the extremes allow builds a multiset with the same buckets and extremes and the least
    /// (greatest) sum: the decoder accepts both sums and refuses one past either.
    #[test]
    fn the_decoder_accepts_exactly_the_sums_between_the_least_and_greatest_witness(
        xs in prop_oneof![clustered(), prop::collection::vec(value(), 1..160)],
    ) {
        let summary = Summary::of(xs.iter().copied());
        let (min, max) = (summary.min().expect("nonempty"), summary.max().expect("nonempty"));
        let buckets: Vec<(u16, u64)> = summary.buckets().collect();
        let mut sorted = xs.clone();
        sorted.sort_unstable();
        let (mut least, mut most) = (vec![min], vec![min]);
        if let [_, inner @ .., _] = sorted.as_slice() {
            for &v in inner {
                let (low, high) = bucket_bounds(bucket_index(v)).expect("in the layout");
                least.push(low.max(min));
                most.push(high.min(max));
            }
            least.push(max);
            most.push(max);
        }
        let (least, most) = (Summary::of(least), Summary::of(most));
        for witness in [&least, &most] {
            prop_assert_eq!(witness.buckets().collect::<Vec<_>>(), buckets.clone());
            prop_assert_eq!((witness.min(), witness.max()), (Some(min), Some(max)));
        }
        let decodes = |sum: u128| Summary::decode(&encode_raw(&buckets, min, max, sum)).is_ok();
        prop_assert!(decodes(least.sum()) && decodes(summary.sum()) && decodes(most.sum()));
        prop_assert!(least.sum() == 0 || !decodes(least.sum() - 1));
        prop_assert!(!decodes(most.sum() + 1));
    }
}

#[test]
fn malformed_and_impossible_summaries_are_refused_with_their_reason() {
    let wide = bucket_index(64) as u8; // [64, 65]
    assert_eq!(bucket_bounds(u16::from(wide)), Some((64, 65)));
    let mut too_many = vec![KIND_SUMMARY, SUMMARY_VERSION];
    put_varint(&mut too_many, u128::from(BUCKET_COUNT) + 1);
    let mut past_layout = vec![KIND_SUMMARY, SUMMARY_VERSION, 1];
    put_varint(&mut past_layout, u128::from(BUCKET_COUNT));
    past_layout.extend([1, 0, 0, 0]);
    let mut second_past_layout = vec![KIND_SUMMARY, SUMMARY_VERSION, 2, 0, 1];
    put_varint(&mut second_past_layout, u128::from(BUCKET_COUNT) - 1);
    second_past_layout.extend([1, 0, 0, 0]);
    let mut wide_u64 = vec![KIND_SUMMARY, SUMMARY_VERSION];
    wide_u64.extend([0xff; 9]);
    wide_u64.push(0x02);
    let mut eleven_bytes = vec![KIND_SUMMARY, SUMMARY_VERSION];
    eleven_bytes.extend([0x80; 10]);
    eleven_bytes.push(0x01);
    let mut wide_sum = vec![KIND_SUMMARY, SUMMARY_VERSION, 1, 0, 1, 0, 0];
    wide_sum.extend([0xff; 18]);
    wide_sum.push(0x04);
    let cases: Vec<(&str, Vec<u8>, DecodeError)> = vec![
        ("no bytes", vec![], DecodeError::Truncated),
        (
            "a kind and no version",
            vec![KIND_SUMMARY],
            DecodeError::Truncated,
        ),
        (
            "a counter is not a summary",
            Counter::new(5).encode(),
            DecodeError::WrongKind {
                expected: KIND_SUMMARY,
                found: KIND_COUNTER,
            },
        ),
        (
            "version 2 is a layout this build does not know",
            vec![KIND_SUMMARY, 2, 0],
            DecodeError::UnknownVersion {
                kind: KIND_SUMMARY,
                version: 2,
            },
        ),
        (
            "a bucket count with a zero tail group",
            vec![KIND_SUMMARY, 1, 0x80, 0x00],
            DecodeError::NonMinimalVarint,
        ),
        (
            "a varint wider than 64 bits",
            wide_u64,
            DecodeError::VarintOverflow,
        ),
        (
            "a varint of eleven bytes",
            eleven_bytes,
            DecodeError::VarintOverflow,
        ),
        (
            "a sum wider than 128 bits",
            wide_sum,
            DecodeError::VarintOverflow,
        ),
        (
            "more buckets than the layout",
            too_many,
            DecodeError::TooManyBuckets,
        ),
        (
            "a bucket past the layout",
            past_layout,
            DecodeError::BucketOutOfRange,
        ),
        (
            "a second bucket past the layout",
            second_past_layout,
            DecodeError::BucketOutOfRange,
        ),
        (
            "an empty bucket",
            vec![KIND_SUMMARY, 1, 1, 5, 0, 5, 5, 0],
            DecodeError::EmptyBucket,
        ),
        (
            "bytes after the empty summary",
            vec![KIND_SUMMARY, 1, 0, 0],
            DecodeError::TrailingBytes,
        ),
        (
            "a minimum below its bucket",
            vec![KIND_SUMMARY, 1, 1, 5, 1, 4, 5, 5],
            DecodeError::MinOutsideBucket,
        ),
        (
            "a maximum above its bucket",
            vec![KIND_SUMMARY, 1, 1, 5, 1, 5, 6, 5],
            DecodeError::MaxOutsideBucket,
        ),
        (
            "a minimum above the maximum",
            vec![KIND_SUMMARY, 1, 1, wide, 2, 65, 64, 0x81, 0x01],
            DecodeError::MinAboveMax,
        ),
        (
            "one value with two extremes",
            vec![KIND_SUMMARY, 1, 1, wide, 1, 64, 65, 64],
            DecodeError::ExtremesExceedCount,
        ),
        (
            "a sum below any two fives",
            vec![KIND_SUMMARY, 1, 1, 5, 2, 5, 5, 9],
            DecodeError::SumOutOfRange,
        ),
        (
            "a sum above any two fives",
            vec![KIND_SUMMARY, 1, 1, 5, 2, 5, 5, 11],
            DecodeError::SumOutOfRange,
        ),
    ];
    let mut cases = cases;
    cases.extend([
        (
            "a minimum above the lowest of two buckets",
            vec![KIND_SUMMARY, 1, 2, 5, 1, 4, 1, 7, 10, 17],
            DecodeError::MinOutsideBucket,
        ),
        (
            "a maximum below the highest of two buckets",
            vec![KIND_SUMMARY, 1, 2, 5, 1, 4, 1, 5, 7, 12],
            DecodeError::MaxOutsideBucket,
        ),
        (
            "any sum but 0 for zeros alone, however many",
            encode_raw(&[(0, u64::MAX)], 0, 0, 5),
            DecodeError::SumOutOfRange,
        ),
        (
            "any sum but 1 for zeros and a single one",
            encode_raw(&[(0, u64::MAX), (1, 1)], 0, 1, 7),
            DecodeError::SumOutOfRange,
        ),
    ]);
    for (why, bytes, expected) in cases {
        assert_eq!(Summary::decode(&bytes), Err(expected), "{why}");
    }
    let mut zeros_and_a_one = Summary::new();
    zeros_and_a_one.record_n(0, u64::MAX);
    zeros_and_a_one.record(1);
    let bytes = encode_raw(&[(0, u64::MAX), (1, 1)], 0, 1, 1);
    assert_eq!(Summary::decode(&bytes), Ok(zeros_and_a_one));
}

#[test]
fn every_unknown_version_and_every_other_kind_is_refused_not_misread() {
    let valid: [(u8, Vec<u8>); 4] = [
        (KIND_SUMMARY, Summary::of([1, 2, 3]).encode()),
        (KIND_COUNTER, Counter::new(3).encode()),
        (KIND_GAUGE, Gauge::new(1, 3).encode()),
        (KIND_ID, id_at(0, "tokens.output", 0).encode()),
    ];
    type Decoder = fn(&[u8]) -> Result<(), DecodeError>;
    let decoders: [(u8, Decoder); 4] = [
        (KIND_SUMMARY, |b| Summary::decode(b).map(drop)),
        (KIND_COUNTER, |b| Counter::decode(b).map(drop)),
        (KIND_GAUGE, |b| Gauge::decode(b).map(drop)),
        (KIND_ID, |b| SummaryId::decode(b).map(drop)),
    ];
    for (kind, bytes) in &valid {
        for (expected, decode) in &decoders {
            if kind == expected {
                assert_eq!(decode(bytes), Ok(()), "kind {kind:#x} decodes as itself");
                for version in (0..=u8::MAX).filter(|&v| v != 1) {
                    let mut other = bytes.clone();
                    other[1] = version;
                    assert_eq!(
                        decode(&other),
                        Err(DecodeError::UnknownVersion {
                            kind: *kind,
                            version
                        }),
                        "kind {kind:#x} version {version}"
                    );
                }
            } else {
                assert_eq!(
                    decode(bytes),
                    Err(DecodeError::WrongKind {
                        expected: *expected,
                        found: *kind
                    }),
                    "kind {kind:#x} read as {expected:#x}"
                );
            }
        }
    }
}

#[test]
fn the_v1_layouts_are_frozen_byte_for_byte() {
    // 1, 64 and 1000 fall in buckets 1, 64 and 190: gaps 1, 62 and 125, one value each,
    // then the minimum 1, the maximum 1000 and the sum 1065.
    assert_eq!(
        Summary::of([1, 64, 1000]).encode(),
        [b'S', 1, 3, 1, 1, 62, 1, 125, 1, 1, 0xe8, 0x07, 0xa9, 0x08]
    );
    assert_eq!(Counter::new(300).encode(), [b'C', 1, 0xac, 0x02]);
    assert_eq!(Gauge::new(1, 300).encode(), [b'G', 1, 0x01, 0xac, 0x02]);
    let mut id = vec![b'I', 1, 18];
    id.extend_from_slice(b"n-0000000000000001");
    id.push(13);
    id.extend_from_slice(b"tokens.output");
    id.push(1);
    put_varint(&mut id, u128::from(MONDAY_2026_11_02_MS / MINUTE));
    assert_eq!(id_at(1, "tokens.output", 0).encode(), id);
}

#[test]
fn the_empty_summary_is_three_bytes_and_the_largest_is_max_summary_len() {
    assert_eq!(Summary::new().encode(), [KIND_SUMMARY, SUMMARY_VERSION, 0]);
    assert_eq!(
        Summary::decode(&[KIND_SUMMARY, SUMMARY_VERSION, 0]),
        Ok(Summary::new())
    );
    let mut largest = Summary::new();
    for index in 0..BUCKET_COUNT {
        let (_, high) = bucket_bounds(index).expect("in the layout");
        largest.record_n(high, u64::MAX);
    }
    assert_eq!(largest.sum(), u128::MAX, "the sum saturates");
    assert_eq!(largest.encoded_len(), MAX_SUMMARY_LEN);
    let bytes = largest.encode();
    assert_eq!(bytes.len(), MAX_SUMMARY_LEN);
    assert_eq!(Summary::decode(&bytes), Ok(largest));
}

// ---------------------------------------------------------------------------
// Windows
// ---------------------------------------------------------------------------

proptest! {
    #[test]
    fn a_window_holds_its_instant_and_nests_in_every_coarser_window(
        at in (4 * DAY)..(1u64 << 52),
        len in window_len(),
    ) {
        let window = Window::containing(at, len).expect("an instant after the first Monday");
        prop_assert!(window.contains(at));
        prop_assert!(window.contains(window.start_ms()));
        prop_assert!(!window.contains(window.end_ms()), "the end is exclusive");
        prop_assert!(!window.contains(window.start_ms() - 1));
        prop_assert_eq!(window.window_len(), len);
        prop_assert_eq!(window.end_ms() - window.start_ms(), len.millis());
        prop_assert_eq!(window.span(), window.start_ms()..window.end_ms());
        prop_assert_eq!(Window::starting(window.start_ms(), len), Some(window));
        prop_assert_eq!(Window::starting(window.start_ms() + 1, len), None);
        prop_assert_eq!(Window::from_index(len, window.index()), Some(window));
        prop_assert_eq!(window.next().map(Window::start_ms), Some(window.end_ms()));
        for coarse in WindowLen::ALL {
            match window.coarsen(coarse) {
                Some(outer) => {
                    prop_assert!(coarse >= len);
                    prop_assert_eq!(outer.window_len(), coarse);
                    prop_assert!(outer.start_ms() <= window.start_ms());
                    prop_assert!(window.end_ms() <= outer.end_ms());
                }
                None => prop_assert!(coarse < len),
            }
        }
    }

    #[test]
    fn rolling_fine_windows_up_equals_summarizing_the_coarse_window_directly(
        events in prop::collection::vec((offset_ms(), value()), 0..200),
        (fine, coarse) in fine_and_coarse(),
    ) {
        let window_of = |offset: u64, len| {
            Window::containing(MONDAY_2026_11_02_MS + offset, len).expect("in range")
        };
        let mut fine_rows: BTreeMap<Window, Summary> = BTreeMap::new();
        let mut direct: BTreeMap<Window, Summary> = BTreeMap::new();
        for &(offset, value) in &events {
            fine_rows.entry(window_of(offset, fine)).or_default().record(value);
            direct.entry(window_of(offset, coarse)).or_default().record(value);
        }
        let mut rolled: BTreeMap<Window, Summary> = BTreeMap::new();
        for (window, summary) in &fine_rows {
            let outer = window.coarsen(coarse).expect("coarser or equal");
            rolled.entry(outer).or_default().merge(summary);
        }
        prop_assert_eq!(rolled, direct);
    }
}

#[test]
fn weeks_start_on_monday_and_days_at_midnight_utc() {
    // Wednesday 2026-11-04 12:34:56.789 UTC.
    let at = MONDAY_2026_11_02_MS + 2 * DAY + 12 * HOUR + 34 * MINUTE + 56_789;
    let start = |len| Window::containing(at, len).map(Window::start_ms);
    assert_eq!(start(WindowLen::Week), Some(MONDAY_2026_11_02_MS));
    assert_eq!(start(WindowLen::Day), Some(MONDAY_2026_11_02_MS + 2 * DAY));
    assert_eq!(
        start(WindowLen::Hour),
        Some(MONDAY_2026_11_02_MS + 2 * DAY + 12 * HOUR)
    );
    assert_eq!(
        start(WindowLen::Minute),
        Some(MONDAY_2026_11_02_MS + 2 * DAY + 12 * HOUR + 34 * MINUTE)
    );
    // The first week began on Monday 1970-01-05; instants before it are in no week.
    assert_eq!(Window::containing(4 * DAY - 1, WindowLen::Week), None);
    assert_eq!(
        Window::containing(4 * DAY, WindowLen::Week).map(Window::index),
        Some(0)
    );
    assert_eq!(
        Window::containing(0, WindowLen::Day).map(Window::index),
        Some(0)
    );
    // A window that would end past u64::MAX does not exist, at any length.
    for len in WindowLen::ALL {
        assert_eq!(Window::containing(u64::MAX, len), None, "{len:?}");
        assert_eq!(Window::from_index(len, u64::MAX), None, "{len:?}");
        let last = Window::containing(u64::MAX - len.millis(), len).expect("ends in range");
        assert_eq!(last.next(), None, "{len:?}: nothing after the last window");
    }
}

// ---------------------------------------------------------------------------
// Names and identity
// ---------------------------------------------------------------------------

#[test]
fn names_are_short_printable_ascii_without_subject_separators() {
    assert_eq!(
        Origin::new("n-0123456789abcdef").map(|o| o.to_string()),
        Ok("n-0123456789abcdef".into())
    );
    assert!(Origin::new("0d3f6c1e-5a2b-4c8d-9e7f-102938475665").is_ok());
    assert_eq!(
        MetricName::new("tokens.cache_read").map(|m| m.as_str().len()),
        Ok(17)
    );
    assert!(MetricName::new(&"m".repeat(MAX_NAME_LEN)).is_ok());
    assert_eq!(
        MetricName::new(&"m".repeat(MAX_NAME_LEN + 1)),
        Err(NameError::TooLong)
    );
    assert_eq!(Origin::new(""), Err(NameError::Empty));
    for (bad, byte) in [
        ("a b", b' '),
        ("a/b", b'/'),
        ("a*", b'*'),
        ("a>", b'>'),
        ("\u{7f}", 0x7f),
        ("é", 0xc3),
        ("a\n", b'\n'),
    ] {
        assert_eq!(MetricName::new(bad), Err(NameError::Byte(byte)), "{bad:?}");
    }
}

fn id_at(n: usize, name: &str, offset: u64) -> SummaryId {
    SummaryId {
        origin: origin(n),
        metric: metric(name),
        window: minute_at(offset),
    }
}

proptest! {
    #[test]
    fn a_summary_id_round_trips_and_its_prefixes_are_refused(
        origin_name in "[a-z0-9:.-]{1,64}",
        metric_name in "[A-Za-z0-9_.]{1,64}",
        (len, index) in (window_len(), any::<u64>())
            .prop_map(|(len, raw)| (len, raw % (u64::MAX / len.millis() - 1))),
    ) {
        let id = SummaryId {
            origin: Origin::new(&origin_name).expect("valid"),
            metric: MetricName::new(&metric_name).expect("valid"),
            window: Window::from_index(len, index).expect("in range"),
        };
        let bytes = id.encode();
        prop_assert_eq!(SummaryId::decode(&bytes), Ok(id));
        for cut in 0..bytes.len() {
            prop_assert!(SummaryId::decode(&bytes[..cut]).is_err());
        }
    }
}

#[test]
fn a_summary_id_naming_no_window_or_an_invalid_name_is_refused() {
    let good = id_at(1, "tokens.output", 0).encode();
    let tag_at = 2 + 1 + 18 + 1 + 13;
    assert_eq!(good[tag_at], 1, "the minute tag follows the two names");
    for tag in [0u8, 5, 0xff] {
        let mut bad = good.clone();
        bad[tag_at] = tag;
        assert_eq!(
            SummaryId::decode(&bad),
            Err(DecodeError::BadWindow),
            "tag {tag}"
        );
    }
    let mut no_window = good[..=tag_at].to_vec();
    put_varint(&mut no_window, u128::from(u64::MAX / MINUTE));
    assert_eq!(SummaryId::decode(&no_window), Err(DecodeError::BadWindow));
    let mut spaced = good.clone();
    spaced[3] = b' ';
    assert_eq!(
        SummaryId::decode(&spaced),
        Err(DecodeError::BadName(NameError::Byte(b' ')))
    );
    let mut empty_name = vec![KIND_ID, 1, 0];
    empty_name.extend_from_slice(&good[3 + 18..]);
    assert_eq!(
        SummaryId::decode(&empty_name),
        Err(DecodeError::BadName(NameError::Empty))
    );
    let mut long_name = vec![KIND_ID, 1, 65];
    long_name.extend(std::iter::repeat_n(b'a', 65));
    long_name.extend_from_slice(&good[3 + 18..]);
    assert_eq!(
        SummaryId::decode(&long_name),
        Err(DecodeError::BadName(NameError::TooLong))
    );
}

// ---------------------------------------------------------------------------
// Rollup
// ---------------------------------------------------------------------------

proptest! {
    /// Each origin writes a minute row per window it saw events in, one version after each
    /// event (revision = how many events of that row it had). Every version reaches the
    /// reader, in a shuffled order and with duplicates, as replication over several paths
    /// delivers them, and the reader may forget minute rows at some point among them. The
    /// reader's views equal the summaries of the raw events in the windows still live.
    #[test]
    fn a_rollup_counts_each_origins_newest_row_once_whatever_the_delivery(
        per_origin in prop::collection::vec(
            prop::collection::vec((offset_ms(), value()), 1..50),
            1..5,
        ),
        seed in any::<u64>(),
        forget in prop::option::of(0u64..11 * DAY),
    ) {
        let tokens = metric("tokens.output");
        let mut offers: Vec<(SummaryId, u64, Summary)> = Vec::new();
        let mut identities = BTreeSet::new();
        for (n, events) in per_origin.iter().enumerate() {
            let mut rows: BTreeMap<Window, (u64, Summary)> = BTreeMap::new();
            for &(offset, value) in events {
                let window = minute_at(offset);
                let (revision, summary) = rows.entry(window).or_insert((0, Summary::new()));
                *revision += 1;
                summary.record(value);
                let id = SummaryId { origin: origin(n), metric: tokens.clone(), window };
                identities.insert(id.clone());
                offers.push((id, *revision, summary.clone()));
            }
        }
        let duplicates: Vec<_> = offers.iter().step_by(3).cloned().collect();
        offers.extend(duplicates);
        // `None` is the forget, delivered at a random point among the rows.
        let horizon = forget.map(|offset| MONDAY_2026_11_02_MS + offset);
        let mut ops: Vec<Option<(SummaryId, u64, Summary)>> =
            offers.iter().cloned().map(Some).collect();
        if horizon.is_some() {
            ops.push(None);
        }
        shuffle(&mut ops, seed);

        let mut rollup = Rollup::new();
        let mut naive = Summary::new();
        for op in ops {
            match op {
                Some((id, revision, summary)) => {
                    naive.merge(&summary);
                    rollup.offer(id, revision, summary);
                }
                None => {
                    rollup.forget_before(WindowLen::Minute, horizon.expect("a forget"));
                }
            }
        }
        let live = |window: &Window| horizon.is_none_or(|at| window.end_ms() > at);
        let live_ids = identities.iter().filter(|id| live(&id.window)).count();
        prop_assert_eq!(rollup.len(), live_ids);
        prop_assert_eq!(rollup.horizon_ms(WindowLen::Minute), horizon.unwrap_or(0));

        let live_events = |events: &[(u64, u64)]| -> Summary {
            Summary::of(
                events.iter().filter(|&&(offset, _)| live(&minute_at(offset))).map(|&(_, v)| v),
            )
        };
        let everything = MONDAY_2026_11_02_MS..MONDAY_2026_11_02_MS + 11 * DAY;
        let merged = rollup.summarize(&tokens, WindowLen::Minute, everything.clone());
        let all: Vec<(u64, u64)> = per_origin.iter().flatten().copied().collect();
        prop_assert_eq!(&merged, &live_events(&all));
        // Negative control: merging every delivered row over-counts as soon as an origin
        // wrote two versions of a row or a row arrived twice.
        prop_assert!(offers.len() > identities.len());
        prop_assert!(naive.count() > all.len() as u64);

        let by_origin = rollup.per_origin(&tokens, WindowLen::Minute, everything);
        for (n, events) in per_origin.iter().enumerate() {
            let own = live_events(events);
            let expected = if own.is_empty() { None } else { Some(&own) };
            prop_assert_eq!(by_origin.get(&origin(n)), expected);
        }

        // A coarser span selects exactly the minutes inside it.
        let first_hour = Window::containing(MONDAY_2026_11_02_MS, WindowLen::Hour).expect("in range");
        let in_hour: Vec<(u64, u64)> = all.iter().copied().filter(|&(offset, _)| offset < HOUR).collect();
        prop_assert_eq!(rollup.summarize(&tokens, WindowLen::Minute, first_hour.span()), live_events(&in_hour));
        prop_assert!(rollup.summarize(&tokens, WindowLen::Hour, first_hour.span()).is_empty());
        prop_assert!(rollup.summarize(&metric("other"), WindowLen::Minute, first_hour.span()).is_empty());

        // Offering every row again, in another order, changes nothing.
        let before = rollup.clone();
        shuffle(&mut offers, seed ^ 0x5555);
        for (id, revision, summary) in offers {
            let expected = if live(&id.window) { Offered::Kept } else { Offered::Expired };
            prop_assert_eq!(rollup.offer(id.clone(), revision, summary), expected);
            prop_assert_eq!(rollup.get(&id), before.get(&id));
        }
        prop_assert_eq!(rollup.len(), before.len());
    }
}

#[test]
fn a_rollup_keeps_the_highest_revision_and_breaks_a_tie_the_same_way_every_time() {
    let id = id_at(7, "tokens.output", 0);
    let older = Summary::of([10, 20]);
    let newer = Summary::of([10]);
    let mut rollup = Rollup::new();
    assert_eq!(rollup.offer(id.clone(), 2, newer.clone()), Offered::Added);
    assert_eq!(rollup.offer(id.clone(), 1, older.clone()), Offered::Kept);
    assert_eq!(
        rollup.get(&id),
        Some((2, &newer)),
        "a higher revision wins even when smaller"
    );
    let newest = Summary::of([10, 30]);
    assert_eq!(
        rollup.offer(id.clone(), 3, newest.clone()),
        Offered::Replaced
    );
    assert_eq!(rollup.get(&id), Some((3, &newest)));
    // Ties: summaries that differ in count, and two that agree on count, sum, minimum and
    // maximum and differ only in their buckets.
    for (a, b) in [
        (older, newer),
        (Summary::of([0, 1, 4, 5]), Summary::of([0, 2, 3, 5])),
    ] {
        let mut forward = Rollup::new();
        forward.offer(id.clone(), 5, a.clone());
        forward.offer(id.clone(), 5, b.clone());
        let mut backward = Rollup::new();
        backward.offer(id.clone(), 5, b);
        backward.offer(id.clone(), 5, a);
        assert_eq!(
            forward.get(&id),
            backward.get(&id),
            "a tie resolves whatever the order"
        );
    }
}

#[test]
fn forgetting_drops_one_lengths_ended_rows_and_refuses_them_from_then_on() {
    let tokens = metric("tokens.output");
    let mut rollup = Rollup::new();
    for n in 0..3 {
        for minute in 0..10 {
            rollup.offer(
                id_at(n, "tokens.output", minute * MINUTE),
                1,
                Summary::of([minute]),
            );
        }
        let hour = Window::containing(MONDAY_2026_11_02_MS, WindowLen::Hour).expect("in range");
        let id = SummaryId {
            origin: origin(n),
            metric: tokens.clone(),
            window: hour,
        };
        rollup.offer(id, 1, Summary::of([1]));
    }
    assert_eq!(rollup.len(), 33);
    let reversed = std::ops::Range {
        start: MONDAY_2026_11_02_MS + HOUR,
        end: MONDAY_2026_11_02_MS,
    };
    let nothing = rollup.summarize(&tokens, WindowLen::Minute, reversed.clone());
    assert!(nothing.is_empty(), "a reversed span selects nothing");
    assert!(rollup
        .per_origin(&tokens, WindowLen::Minute, reversed)
        .is_empty());
    let minute = WindowLen::Minute;
    assert_eq!(
        rollup.forget_before(minute, MONDAY_2026_11_02_MS + 5 * MINUTE),
        15
    );
    assert_eq!(rollup.len(), 18);
    assert_eq!(rollup.get(&id_at(0, "tokens.output", 4 * MINUTE)), None);
    assert!(rollup.get(&id_at(0, "tokens.output", 5 * MINUTE)).is_some());
    // A late stale copy of a forgotten row is refused, and a horizon only moves forward.
    let stale = rollup.offer(id_at(0, "tokens.output", 4 * MINUTE), 0, Summary::of([4]));
    assert_eq!(stale, Offered::Expired);
    assert_eq!(rollup.len(), 18);
    assert_eq!(rollup.forget_before(minute, MONDAY_2026_11_02_MS), 0);
    assert_eq!(rollup.horizon_ms(minute), MONDAY_2026_11_02_MS + 5 * MINUTE);
    assert_eq!(
        rollup.forget_before(minute, MONDAY_2026_11_02_MS + 5 * MINUTE),
        0,
        "nothing more ended"
    );
    // Forgetting minute rows leaves the hour rows a coarser view reads.
    assert_eq!(
        rollup.forget_before(minute, MONDAY_2026_11_02_MS + HOUR),
        15
    );
    assert_eq!(rollup.len(), 3);
    let hour = Window::containing(MONDAY_2026_11_02_MS, WindowLen::Hour).expect("in range");
    assert_eq!(
        rollup
            .summarize(&tokens, WindowLen::Hour, hour.span())
            .count(),
        3
    );
    assert_eq!(rollup.horizon_ms(WindowLen::Hour), 0);
    assert_eq!(
        rollup.forget_before(WindowLen::Hour, MONDAY_2026_11_02_MS + HOUR),
        3
    );
    assert!(rollup.is_empty());
    // A row whose window ends after its length's horizon is still taken.
    let live = rollup.offer(id_at(0, "tokens.output", HOUR), 1, Summary::of([7]));
    assert_eq!(live, Offered::Added);
}

// ---------------------------------------------------------------------------
// Counters and gauges
// ---------------------------------------------------------------------------

fn counter() -> impl Strategy<Value = Counter> {
    any::<u64>().prop_map(Counter::new)
}

fn gauge() -> impl Strategy<Value = Gauge> {
    (0u64..4, 0u64..4).prop_map(|(at, value)| Gauge::new(at, value))
}

proptest! {
    #[test]
    fn counter_and_gauge_joins_are_idempotent_commutative_and_associative(
        a in counter(), b in counter(), c in counter(),
        x in gauge(), y in gauge(), z in gauge(),
    ) {
        prop_assert_eq!(a.join(a), a);
        prop_assert_eq!(a.join(b), b.join(a));
        prop_assert_eq!(a.join(b).join(c), a.join(b.join(c)));
        prop_assert_eq!(a.join(b).total(), a.total().max(b.total()));
        prop_assert_eq!(Counter::ZERO.join(a), a);
        prop_assert_eq!(x.join(x), x);
        prop_assert_eq!(x.join(y), y.join(x));
        prop_assert_eq!(x.join(y).join(z), x.join(y.join(z)));
        let later = x.join(y);
        prop_assert!(later.at_ms() >= x.at_ms() && later.at_ms() >= y.at_ms());
    }

    #[test]
    fn counters_and_gauges_round_trip_and_refuse_their_prefixes(a in counter(), x in (any::<u64>(), any::<u64>())) {
        let gauge = Gauge::new(x.0, x.1);
        prop_assert_eq!(Counter::decode(&a.encode()), Ok(a));
        prop_assert_eq!(Gauge::decode(&gauge.encode()), Ok(gauge));
        for cut in 0..a.encode().len() {
            prop_assert!(Counter::decode(&a.encode()[..cut]).is_err());
        }
        for cut in 0..gauge.encode().len() {
            prop_assert!(Gauge::decode(&gauge.encode()[..cut]).is_err());
        }
        let mut longer = gauge.encode();
        longer.push(0);
        prop_assert_eq!(Gauge::decode(&longer), Err(DecodeError::TrailingBytes));
    }

    /// Each origin's counter only grows; every version it wrote reaches the reader, out of
    /// order and some twice. The joined fleet total is the sum of each origin's last total.
    #[test]
    fn a_fleet_total_of_joined_counters_never_double_counts(
        increments in prop::collection::vec(prop::collection::vec(0u64..1_000_000, 1..20), 1..5),
        seed in any::<u64>(),
    ) {
        let mut versions: Vec<(usize, Counter)> = Vec::new();
        let mut finals = 0u128;
        for (n, steps) in increments.iter().enumerate() {
            let mut counter = Counter::ZERO;
            for &step in steps {
                counter = counter.add(step);
                versions.push((n, counter));
            }
            finals += u128::from(counter.total());
        }
        let again: Vec<_> = versions.iter().step_by(2).copied().collect();
        versions.extend(again);
        shuffle(&mut versions, seed);
        let mut held: BTreeMap<usize, Counter> = BTreeMap::new();
        for (n, counter) in versions {
            let joined = held.get(&n).copied().unwrap_or(Counter::ZERO).join(counter);
            held.insert(n, joined);
        }
        prop_assert_eq!(held.values().map(|c| u128::from(c.total())).sum::<u128>(), finals);
    }
}

#[test]
fn a_gauge_keeps_the_later_reading_and_a_counter_saturates() {
    let earlier = Gauge::new(1_000, 97);
    let later = Gauge::new(2_000, 12);
    assert_eq!(
        earlier.join(later),
        later,
        "a quota percent read later wins though smaller"
    );
    assert_eq!(later.join(earlier).value(), 12);
    assert_eq!(
        Gauge::new(5, 3).join(Gauge::new(5, 4)),
        Gauge::new(5, 4),
        "a tie takes the larger"
    );
    assert_eq!(Counter::new(u64::MAX - 1).add(5).total(), u64::MAX);
    assert_eq!(Counter::new(300).encode(), [KIND_COUNTER, 1, 0xac, 0x02]);
}

// ---------------------------------------------------------------------------
// A day of real agent turns
// ---------------------------------------------------------------------------

/// Output tokens of 96 agent turns over one working day on one Mac: short answers, tool
/// calls, patches and a few long refactors.
const TURN_OUTPUT_TOKENS: [u64; 96] = [
    412, 1_873, 96, 2_304, 655, 3_120, 188, 940, 7_412, 1_056, 233, 4_871, 1_390, 87, 2_618, 512,
    9_840, 1_204, 366, 2_045, 15_320, 731, 1_588, 142, 3_977, 820, 2_266, 61, 1_145, 5_630, 948,
    274, 1_732, 12_004, 403, 2_891, 1_067, 159, 6_215, 788, 1_942, 3_355, 520, 118, 2_480, 1_301,
    31_870, 692, 1_811, 4_406, 255, 977, 2_133, 8_670, 1_486, 333, 1_620, 2_754, 74, 1_099, 3_688,
    610, 22_416, 1_257, 447, 1_934, 5_102, 866, 2_372, 193, 1_418, 3_041, 709, 10_233, 1_560, 298,
    2_087, 1_779, 4_150, 561, 1_336, 128, 2_960, 7_045, 914, 1_665, 381, 2_513, 1_190, 6_644, 470,
    1_888, 3_276, 1_011, 236, 2_199,
];

/// Cache-read input tokens of the same turns: the context each turn re-read, growing
/// through a session and falling back after each compaction.
const TURN_CACHE_READ_TOKENS: [u64; 96] = [
    18_204, 21_377, 24_950, 29_811, 33_406, 38_120, 41_985, 47_302, 52_668, 58_014, 61_779, 67_250,
    72_903, 78_441, 83_120, 89_675, 95_208, 101_334, 108_920, 114_073, 121_655, 128_310, 135_902,
    142_117, 149_860, 156_203, 163_778, 171_045, 178_392, 184_906, 19_533, 23_871, 27_402, 32_955,
    36_184, 41_620, 46_093, 50_877, 56_301, 61_948, 66_502, 72_219, 77_806, 83_390, 88_027, 94_615,
    99_160, 105_844, 111_273, 118_009, 124_660, 131_587, 137_014, 144_925, 151_338, 158_701,
    165_046, 172_833, 179_270, 186_514, 17_890, 22_416, 26_053, 30_788, 35_201, 39_964, 44_317,
    49_082, 53_970, 59_406, 64_118, 69_853, 75_221, 80_694, 86_309, 91_877, 97_430, 103_962,
    109_515, 116_088, 122_751, 129_304, 136_669, 143_027, 150_412, 157_985, 164_330, 171_896,
    178_205, 185_640, 20_117, 24_502, 28_966, 33_740, 38_815, 43_299,
];

#[test]
fn a_day_of_agent_token_counts_reads_back_within_the_bound_in_a_few_hundred_bytes() {
    let output = metric("tokens.output");
    let cache_read = metric("tokens.cache_read");
    let workday = MONDAY_2026_11_02_MS + 2 * DAY + 9 * HOUR;
    let day = Window::containing(workday, WindowLen::Day).expect("in range");
    let mut rollup = Rollup::new();
    let mut largest_minute_row = 0usize;
    // Two Macs ran the same kinds of turns, the second in the reverse order, one turn every
    // five minutes from 09:00 UTC; each wrote one minute row per turn.
    for mac in 0..2 {
        for turn in 0..96 {
            let at = workday + turn as u64 * 5 * MINUTE;
            let window = Window::containing(at, WindowLen::Minute).expect("in range");
            let pick = if mac == 0 { turn } else { 95 - turn };
            for (name, counts) in [
                (&output, &TURN_OUTPUT_TOKENS),
                (&cache_read, &TURN_CACHE_READ_TOKENS),
            ] {
                let row = Summary::of([counts[pick]]);
                largest_minute_row = largest_minute_row.max(row.encoded_len());
                let id = SummaryId {
                    origin: origin(mac),
                    metric: name.clone(),
                    window,
                };
                rollup.offer(id, 1, row);
            }
        }
    }
    // The sizes the module docs state.
    assert_eq!(largest_minute_row, 15, "a one-turn minute row");
    let day_id = SummaryId {
        origin: origin(0),
        metric: output.clone(),
        window: day,
    };
    assert_eq!(day_id.encode().len(), 39, "a node-id origin's day id");
    for (name, counts, bytes, buckets) in [
        (&output, &TURN_OUTPUT_TOKENS, 194, 92),
        (&cache_read, &TURN_CACHE_READ_TOKENS, 158, 72),
    ] {
        let fleet_day = rollup.summarize(name, WindowLen::Minute, day.span());
        let mut sorted: Vec<u64> = counts.iter().chain(counts.iter()).copied().collect();
        sorted.sort_unstable();
        assert_eq!(fleet_day.count(), 192);
        assert_eq!(
            fleet_day.sum(),
            2 * counts.iter().map(|&c| u128::from(c)).sum::<u128>()
        );
        assert_eq!(fleet_day.min(), sorted.first().copied());
        assert_eq!(fleet_day.max(), sorted.last().copied());
        for q in [Quantile::P50, Quantile::P90, Quantile::P95, Quantile::P99] {
            let exact = sorted[q.rank(192) as usize - 1];
            let read = fleet_day.quantile(q).expect("nonempty");
            assert!(
                read.abs_diff(exact) * QUANTILE_ERROR_DIVISOR <= exact,
                "{name} {q:?}: read {read}, exact {exact}"
            );
        }
        assert_eq!(fleet_day.encode().len(), bytes, "{name}: the fleet's day");
        assert_eq!(
            fleet_day.buckets().count(),
            buckets,
            "{name}: the fleet's day"
        );
        let per_mac = rollup.per_origin(name, WindowLen::Minute, day.span());
        assert_eq!(per_mac.len(), 2);
        assert_eq!(
            per_mac.get(&origin(0)),
            per_mac.get(&origin(1)),
            "the same turns"
        );
    }
}
